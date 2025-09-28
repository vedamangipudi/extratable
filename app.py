# app.py
import csv
import io
from collections import defaultdict, Counter
from flask import Flask, render_template, request, redirect, send_file, url_for
import pandas as pd
import math

# Try to import reportlab for PDF export; handle absence gracefully
PDF_AVAILABLE = True
try:
    from reportlab.lib.pagesizes import A4, landscape
    from reportlab.lib import colors
    from reportlab.platypus import SimpleDocTemplate, Table, TableStyle, Paragraph, Spacer
    from reportlab.lib.styles import getSampleStyleSheet
except Exception:
    PDF_AVAILABLE = False

app = Flask(__name__)

# Config
DAYS = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
PERIODS = 6
SLOTS_PER_WEEK = len(DAYS) * PERIODS  # 30

# In-memory store
STORE = {
    "teachers": {},  # teacher_name -> {"subjects": set(), "grades": set()}
    "class_requirements": defaultdict(dict),  # class -> {subject: periods}
    "timetable": {},  # class -> {day: [ (subject, teacher) ... ] }
    "teacher_schedule": {},  # teacher -> {day: [ (class, subject) or None ] }
}

# ---------------------------
# CSV helpers
# ---------------------------
def split_multi(cell):
    if cell is None:
        return []
    if isinstance(cell, (int, float)):
        return [str(int(cell))]
    s = str(cell).strip()
    if not s or s.lower() == 'nan':
        return []
    for sep in [';', '|', ',']:
        if sep in s:
            return [p.strip() for p in s.split(sep) if p.strip()]
    return [s]

def parse_teachers_csv(stream):
    df = pd.read_csv(stream)
    df.columns = [c.strip().lower() for c in df.columns]
    col_map = {}
    for c in df.columns:
        if 'teacher' in c:
            col_map['teacher'] = c
        elif 'subject' in c:
            col_map['subject'] = c
        elif 'grade' in c or 'class' in c:
            col_map.setdefault('grade', c)
    if 'teacher' not in col_map or 'subject' not in col_map:
        raise ValueError("Teachers CSV must include 'Teacher' and 'Subject' columns.")
    teachers = {}
    for _, row in df.iterrows():
        t = str(row[col_map['teacher']]).strip()
        if not t or t.lower() == 'nan':
            continue
        subs = split_multi(row[col_map['subject']]) if col_map.get('subject') else []
        grades = split_multi(row[col_map['grade']]) if col_map.get('grade') else []
        if t not in teachers:
            teachers[t] = {"subjects": set(), "grades": set()}
        teachers[t]["subjects"].update(subs)
        teachers[t]["grades"].update(grades)
    return teachers

def parse_classes_csv(stream):
    df = pd.read_csv(stream)
    df.columns = [c.strip().lower() for c in df.columns]
    col_map = {}
    for c in df.columns:
        if 'class' in c:
            col_map['class'] = c
        elif 'subject' in c:
            col_map['subject'] = c
        elif 'period' in c:
            col_map['periods'] = c
    if 'class' not in col_map or 'subject' not in col_map:
        raise ValueError("Classes CSV must include 'Class' and 'Subject' columns (Periods optional).")
    class_reqs = defaultdict(lambda: defaultdict(int))
    for _, row in df.iterrows():
        classes = split_multi(row[col_map['class']]) if col_map.get('class') else []
        subjects = split_multi(row[col_map['subject']]) if col_map.get('subject') else []
        periods_list = []
        if col_map.get('periods'):
            cell = row[col_map['periods']]
            if not (cell is None or (isinstance(cell, float) and math.isnan(cell))):
                periods_list = [int(x) for x in split_multi(cell)]
        max_len = max(len(classes), len(subjects), len(periods_list) if periods_list else 1)
        if len(classes) == 1 and max_len > 1:
            classes = classes * max_len
        if len(subjects) == 1 and max_len > 1:
            subjects = subjects * max_len
        if len(periods_list) == 1 and max_len > 1:
            periods_list = periods_list * max_len
        for i in range(max_len):
            cls = classes[i] if i < len(classes) else classes[-1]
            sub = subjects[i] if i < len(subjects) else subjects[-1]
            per = int(periods_list[i]) if i < len(periods_list) else None
            if cls and sub:
                if per is None:
                    # mark with 0 for now; will distribute evenly later
                    class_reqs[cls][sub] += 0
                else:
                    class_reqs[cls][sub] += per
    return class_reqs

# ---------------------------
# Scheduler: deterministic heuristic
# ---------------------------
def prepare_distribution():
    # For each class, ensure total periods sum to SLOTS_PER_WEEK by distributing evenly if missing
    for cls, subs in STORE['class_requirements'].items():
        total_assigned = sum(v for v in subs.values() if v > 0)
        subjects = list(subs.keys())
        if total_assigned >= SLOTS_PER_WEEK:
            # If equal or overflow, scale down proportionally if >SLOTS_PER_WEEK
            if total_assigned > SLOTS_PER_WEEK:
                # scale down proportionally (floor), then fix remainder
                scaled = {}
                for s, cnt in subs.items():
                    scaled[s] = max(0, (cnt * SLOTS_PER_WEEK) // total_assigned)
                rem = SLOTS_PER_WEEK - sum(scaled.values())
                # distribute remainder round-robin
                idx = 0
                while rem > 0 and subjects:
                    scaled[subjects[idx % len(subjects)]] += 1
                    idx += 1
                    rem -= 1
                STORE['class_requirements'][cls] = scaled
            else:
                # exactly fits
                pass
        else:
            # Need to fill remaining slots evenly among subjects (including those with 0)
            remaining = SLOTS_PER_WEEK - total_assigned
            # Create list of subjects to distribute: all subjects
            subs_list = subjects.copy()
            base = remaining // len(subs_list) if subs_list else 0
            extra = remaining - base * len(subs_list)
            for s in subs_list:
                STORE['class_requirements'][cls][s] = STORE['class_requirements'][cls].get(s, 0) + base
            # distribute extras deterministically by subject name sorted
            for s in sorted(subs_list)[:extra]:
                STORE['class_requirements'][cls][s] += 1

def assign_teachers_for_subjects():
    """
    Build a mapping subject -> list of teachers who can teach it.
    For assignment, we pick the teacher deterministically:
    - prefer teachers whose 'grades' include the class name or prefix
    - otherwise pick the first teacher alphabetically
    """
    subject_teachers = defaultdict(list)
    for tname, info in STORE['teachers'].items():
        for sub in info['subjects']:
            subject_teachers[sub].append(tname)
    return subject_teachers

def init_empty_structures():
    # Clear timetables and teacher schedules
    STORE['timetable'] = {}
    STORE['teacher_schedule'] = {}
    for teacher in STORE['teachers'].keys():
        STORE['teacher_schedule'][teacher] = {day: [None]*PERIODS for day in DAYS}
    for cls in STORE['class_requirements'].keys():
        STORE['timetable'][cls] = {day: [None]*PERIODS for day in DAYS}

def choose_teacher_for(cls, subject, subject_teachers):
    """Deterministic pick of teacher for (class, subject)."""
    candidates = subject_teachers.get(subject, [])
    if not candidates:
        return None
    # prefer teacher whose grades likely match class (exact or prefix)
    matches = []
    for t in sorted(candidates):
        grades = STORE['teachers'][t]['grades']
        if not grades:
            continue
        for g in grades:
            if cls.startswith(g) or g == cls:
                matches.append(t)
                break
    if matches:
        return matches[0]
    # else first alphabetically
    return sorted(candidates)[0]

def schedule():
    """
    Deterministic greedy scheduler with progressive relaxation.
    - For each day and period, iterate classes in sorted order and try to pick a subject for that slot.
    - Respect constraints:
      * No same subject repeated in same day (prefer)
      * No back-to-back same subject
      * Teacher must be free that slot
      * Teacher must have at least 1 free period per day (we enforce by limiting max daily assignments to PERIODS-1)
    - If impossible at a strict level, we relax constraints in steps.
    """
    prepare_distribution()
    subject_teachers = assign_teachers_for_subjects()
    init_empty_structures()

    # Build remaining counts per class
    remaining = {cls: dict(subs) for cls, subs in STORE['class_requirements'].items()}
    classes = sorted(remaining.keys())

    # compute teacher daily max assignments to ensure at least 1 break per day
    teacher_daily_max = {t: PERIODS - 1 for t in STORE['teachers'].keys()}

    # helper to count assigned for teacher on a day
    def teacher_assigned_count(t, day):
        return sum(1 for x in STORE['teacher_schedule'][t][day] if x is not None)

    # Constraint relaxation levels
    relax_levels = [
        {"allow_same_day": False, "allow_back_to_back": False},
        {"allow_same_day": True, "allow_back_to_back": False},
        {"allow_same_day": True, "allow_back_to_back": True},
    ]

    # deterministic ordering for subject choice: pick subject with largest remaining first, then alphabetical
    def candidate_subjects_for(cls, allow_same_day, allow_back_to_back, day, period):
        cand = [s for s, cnt in remaining[cls].items() if cnt > 0]
        # filter same day
        if not allow_same_day:
            today = set(x[0] for x in STORE['timetable'][cls][day] if x)
            cand = [s for s in cand if s not in today]
        # filter back-to-back
        if not allow_back_to_back:
            if period > 0:
                prev = STORE['timetable'][cls][day][period-1]
                if prev:
                    cand = [s for s in cand if s != prev[0]]
        # sort by remaining desc then name
        cand.sort(key=lambda x: (-remaining[cls][x], x))
        return cand

    # Try scheduling with increasing relaxation until all slots filled or no improvement
    for level in relax_levels:
        changed = True
        # iterate days and periods deterministically
        for day in DAYS:
            for period in range(PERIODS):
                for cls in classes:
                    # if already filled skip
                    if STORE['timetable'][cls][day][period] is not None:
                        continue
                    if sum(remaining[cls].values()) == 0:
                        continue  # nothing left to place
                    # pick a subject
                    subjects = candidate_subjects_for(cls, level["allow_same_day"], level["allow_back_to_back"], day, period)
                    assigned = False
                    for sub in subjects:
                        teacher = choose_teacher_for(cls, sub, subject_teachers)
                        if teacher is None:
                            continue
                        # teacher must be free at (day,period)
                        if STORE['teacher_schedule'][teacher][day][period] is not None:
                            continue
                        # teacher must not exceed daily max
                        if teacher_assigned_count(teacher, day) >= teacher_daily_max.get(teacher, PERIODS - 1):
                            continue
                        # assign
                        STORE['timetable'][cls][day][period] = (sub, teacher)
                        STORE['teacher_schedule'][teacher][day][period] = (cls, sub)
                        remaining[cls][sub] -= 1
                        assigned = True
                        break
                    # if not assigned in this level, leave for more relaxed level
    # After relaxation levels, fill any remaining empty class slots allowing any assignments if possible
    # Try permissive fill: allow same-day and back-to-back and allow teachers to exceed daily max if unavoidable
    for day in DAYS:
        for period in range(PERIODS):
            for cls in classes:
                if STORE['timetable'][cls][day][period] is not None:
                    continue
                if sum(remaining[cls].values()) == 0:
                    # if still empty but no remaining, pick any subject from class requirements (fallback)
                    possible = list(STORE['class_requirements'][cls].keys())
                    if not possible:
                        continue
                    sub = sorted(possible)[0]
                else:
                    # pick subject with remaining (largest)
                    subs = sorted([s for s, cnt in remaining[cls].items() if cnt > 0], key=lambda x: (-remaining[cls][x], x))
                    if not subs:
                        subs = sorted(STORE['class_requirements'][cls].keys())
                    sub = subs[0]
                teacher = choose_teacher_for(cls, sub, subject_teachers)
                if teacher is None:
                    # leave blank (should be rare)
                    continue
                # find a teacher free slot possibly by forcing (allow teacher exceed daily)
                if STORE['teacher_schedule'][teacher][day][period] is None:
                    STORE['timetable'][cls][day][period] = (sub, teacher)
                    STORE['teacher_schedule'][teacher][day][period] = (cls, sub)
                    if remaining[cls].get(sub, 0) > 0:
                        remaining[cls][sub] -= 1
                else:
                    # teacher busy — try another teacher for same subject
                    alt_teachers = sorted([t for t in assign_teachers_for_subjects().get(sub, []) if STORE['teacher_schedule'].get(t)])
                    placed = False
                    for t in alt_teachers:
                        if STORE['teacher_schedule'][t][day][period] is None:
                            STORE['timetable'][cls][day][period] = (sub, t)
                            STORE['teacher_schedule'][t][day][period] = (cls, sub)
                            if remaining[cls].get(sub, 0) > 0:
                                remaining[cls][sub] -= 1
                            placed = True
                            break
                    if not placed:
                        # leave blank if nothing works
                        pass

    # Final pass: if any teacher has zero free periods some day (violates break), try to enforce at least one break by swapping
    for teacher in sorted(STORE['teacher_schedule'].keys()):
        for day in DAYS:
            assigned_count = sum(1 for x in STORE['teacher_schedule'][teacher][day] if x)
            if assigned_count >= PERIODS:
                # try to find a period to vacate by swapping that teacher's slot with another class's slot at same period
                for period in range(PERIODS):
                    entry = STORE['teacher_schedule'][teacher][day][period]
                    if entry is None:
                        continue
                    cls, sub = entry
                    # look for another period in same day for same class where some other teacher is assigned that can swap
                    for alt_period in range(PERIODS):
                        if alt_period == period:
                            continue
                        alt_entry = STORE['timetable'][cls][day][alt_period]
                        if alt_entry is None:
                            # move teacher's subject to alt_period if teacher free at alt_period
                            if STORE['teacher_schedule'][teacher][day][alt_period] is None:
                                STORE['timetable'][cls][day][alt_period] = (sub, teacher)
                                STORE['timetable'][cls][day][period] = None
                                STORE['teacher_schedule'][teacher][day][alt_period] = (cls, sub)
                                STORE['teacher_schedule'][teacher][day][period] = None
                                break
                        else:
                            other_sub, other_teacher = alt_entry
                            # see if swapping teachers keeps teacher availability
                            if STORE['teacher_schedule'][other_teacher][day][period] is None and STORE['teacher_schedule'][teacher][day][alt_period] is None:
                                # perform swap
                                STORE['timetable'][cls][day][alt_period] = (sub, teacher)
                                STORE['timetable'][cls][day][period] = (other_sub, other_teacher)
                                STORE['teacher_schedule'][teacher][day][alt_period] = (cls, sub)
                                STORE['teacher_schedule'][other_teacher][day][period] = (cls, other_sub)
                                STORE['teacher_schedule'][teacher][day][period] = None
                                break

# ---------------------------
# Routes
# ---------------------------
@app.route('/', methods=['GET', 'POST'])
def index():
    message = None
    if request.method == 'POST':
        teachers_file = request.files.get('teachers_csv')
        classes_file = request.files.get('classes_csv')
        if not teachers_file or teachers_file.filename == '':
            message = "Please upload Teachers CSV."
        elif not classes_file or classes_file.filename == '':
            message = "Please upload Classes CSV."
        else:
            try:
                teachers = parse_teachers_csv(teachers_file)
                class_reqs = parse_classes_csv(classes_file)
                # store
                STORE['teachers'].clear()
                STORE['teachers'].update(teachers)
                STORE['class_requirements'].clear()
                for cls, subs in class_reqs.items():
                    STORE['class_requirements'][cls] = dict(subs)
                # If a class had subjects listed with 0 counts, ensure they exist (distribute later)
                # For classes with no provided periods, those subject counts are currently 0 and will be distributed in prepare_distribution()
                # Run scheduler
                schedule()
                return redirect(url_for('timetable_view'))
            except Exception as e:
                message = f"Error: {e}"
    return render_template('index.html', message=message)

@app.route('/timetable')
def timetable_view():
    classes = sorted(list(STORE['class_requirements'].keys()))
    teachers = sorted(list(STORE['teachers'].keys()))
    return render_template('timetable.html',
                           days=DAYS, periods=list(range(1, PERIODS+1)),
                           classes=classes, teachers=teachers,
                           timetable=STORE['timetable'],
                           teacher_schedule=STORE['teacher_schedule'])

# CSV download: per-class CSVs zipped into single CSV (multi-class)
@app.route('/download/csv')
def download_csv():
    output = io.StringIO()
    writer = csv.writer(output)
    header = ["Class", "Day"] + [f"P{p}" for p in range(1, PERIODS+1)]
    writer.writerow(header)
    for cls, daymap in STORE['timetable'].items():
        for day in DAYS:
            row = [cls, day]
            for p in range(PERIODS):
                cell = daymap[day][p]
                if cell:
                    subject, teacher = cell
                    row.append(f"{subject} ({teacher})")
                else:
                    row.append("")
            writer.writerow(row)
    output.seek(0)
    return send_file(io.BytesIO(output.getvalue().encode()), mimetype='text/csv', as_attachment=True, download_name='timetable_all_classes.csv')

# PDF downloads: one PDF per class and one per teacher, returned as single PDF with pages for each
@app.route('/download/pdf')
def download_pdf():
    if not PDF_AVAILABLE:
        return "PDF export unavailable: reportlab not installed. Install with `pip install reportlab`", 500
    buffer = io.BytesIO()
    doc = SimpleDocTemplate(buffer, pagesize=landscape(A4), rightMargin=10, leftMargin=10, topMargin=10, bottomMargin=10)
    elements = []
    styles = getSampleStyleSheet()
    # per-class pages
    for cls, daymap in STORE['timetable'].items():
        elements.append(Paragraph(f"Class: {cls}", styles['Heading2']))
        data = []
        header = ["Day"] + [f"P{p}" for p in range(1, PERIODS+1)]
        data.append(header)
        for day in DAYS:
            row = [day]
            for p in range(PERIODS):
                cell = daymap[day][p]
                if cell:
                    subject, teacher = cell
                    row.append(f"{subject}\n({teacher})")
                else:
                    row.append("")
            data.append(row)
        t = Table(data, repeatRows=1)
        t.setStyle(TableStyle([
            ('BACKGROUND', (0,0), (-1,0), colors.HexColor("#f0f0f0")),
            ('GRID', (0,0), (-1,-1), 0.5, colors.black),
            ('ALIGN', (0,0), (-1,-1), 'CENTER'),
            ('VALIGN', (0,0), (-1,-1), 'MIDDLE'),
            ('FONTNAME', (0,0), (-1,0), 'Helvetica-Bold'),
        ]))
        elements.append(t)
        elements.append(Spacer(1, 12))
    # per-teacher pages
    for teacher, daymap in STORE['teacher_schedule'].items():
        elements.append(Paragraph(f"Teacher: {teacher}", styles['Heading2']))
        data = []
        header = ["Day"] + [f"P{p}" for p in range(1, PERIODS+1)]
        data.append(header)
        for day in DAYS:
            row = [day]
            for p in range(PERIODS):
                cell = daymap[day][p]
                if cell:
                    cls, subject = cell
                    row.append(f"{cls}\n({subject})")
                else:
                    row.append("")
            data.append(row)
        t = Table(data, repeatRows=1)
        t.setStyle(TableStyle([
            ('BACKGROUND', (0,0), (-1,0), colors.HexColor("#f0f0f0")),
            ('GRID', (0,0), (-1,-1), 0.5, colors.black),
            ('ALIGN', (0,0), (-1,-1), 'CENTER'),
            ('VALIGN', (0,0), (-1,-1), 'MIDDLE'),
            ('FONTNAME', (0,0), (-1,0), 'Helvetica-Bold'),
        ]))
        elements.append(t)
        elements.append(Spacer(1, 12))
    doc.build(elements)
    buffer.seek(0)
    return send_file(buffer, mimetype='application/pdf', as_attachment=True, download_name='timetables.pdf')

if __name__ == '__main__':
    app.run(debug=True)


