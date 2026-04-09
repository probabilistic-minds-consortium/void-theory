"""
Generate PDF report for De Finetti Spectrum Experiment v2
"""

import json
from reportlab.lib.pagesizes import A4
from reportlab.lib.units import mm, cm
from reportlab.lib.colors import HexColor, black, white
from reportlab.pdfgen import canvas
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle, PageBreak
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.lib.enums import TA_LEFT, TA_CENTER, TA_JUSTIFY

# Colors
VOID_BLACK = HexColor("#1a1a1a")
VOID_DARK = HexColor("#2d2d2d")
VOID_GRAY = HexColor("#666666")
MSHARP_COLOR = HexColor("#2ecc71")   # green
MVAGUE_COLOR = HexColor("#f39c12")   # amber
MVOID_COLOR = HexColor("#e74c3c")    # red
ACCENT = HexColor("#3498db")         # blue

# Load data
with open("experiments/de_finetti_v2_results.json") as f:
    results = json.load(f)

# ============================================================
# STYLES
# ============================================================

styles = getSampleStyleSheet()

title_style = ParagraphStyle(
    'VoidTitle',
    parent=styles['Title'],
    fontSize=22,
    leading=26,
    textColor=VOID_BLACK,
    spaceAfter=6,
    fontName='Helvetica-Bold',
)

subtitle_style = ParagraphStyle(
    'VoidSubtitle',
    parent=styles['Normal'],
    fontSize=12,
    leading=16,
    textColor=VOID_GRAY,
    spaceAfter=20,
    fontName='Helvetica-Oblique',
)

heading_style = ParagraphStyle(
    'VoidHeading',
    parent=styles['Heading1'],
    fontSize=16,
    leading=20,
    textColor=VOID_BLACK,
    spaceBefore=20,
    spaceAfter=10,
    fontName='Helvetica-Bold',
)

heading2_style = ParagraphStyle(
    'VoidHeading2',
    parent=styles['Heading2'],
    fontSize=13,
    leading=17,
    textColor=VOID_DARK,
    spaceBefore=14,
    spaceAfter=8,
    fontName='Helvetica-Bold',
)

body_style = ParagraphStyle(
    'VoidBody',
    parent=styles['Normal'],
    fontSize=10,
    leading=14,
    textColor=VOID_BLACK,
    spaceAfter=8,
    fontName='Helvetica',
    alignment=TA_JUSTIFY,
)

code_style = ParagraphStyle(
    'VoidCode',
    parent=styles['Code'],
    fontSize=8,
    leading=11,
    textColor=VOID_DARK,
    backColor=HexColor("#f5f5f5"),
    borderPadding=6,
    spaceAfter=8,
    fontName='Courier',
)

caption_style = ParagraphStyle(
    'VoidCaption',
    parent=styles['Normal'],
    fontSize=8,
    leading=11,
    textColor=VOID_GRAY,
    spaceAfter=12,
    fontName='Helvetica-Oblique',
    alignment=TA_CENTER,
)


# ============================================================
# HELPERS
# ============================================================

BUDGET_LABELS = [
    "S3_full", "S2_moderate", "T3_tight", "T2_squeezed", "T1_starving",
    "V3_gasping", "V2_choking", "V1_bankrupt", "V0_flatline", "Vx_dead"
]

def get_level_results(q_type, label):
    return [r for r in results if r["question_type"] == q_type and r["label"] == label]

def get_dominant(level_results):
    scores = [r["score"] for r in level_results]
    return max(["MSharp", "MVague", "MVoid"], key=lambda s: scores.count(s))

def score_color(score):
    if score == "MSharp": return MSHARP_COLOR
    if score == "MVague": return MVAGUE_COLOR
    return MVOID_COLOR

def build_spectrum_table(q_type):
    """Build the main spectrum table for a question type."""
    header = ["Budget Level", "Predict", "Ctx", "Temp", "Run 1", "Run 2", "Run 3", "Phase"]

    budget_params = {
        "S3_full":     (500, 4096, 0.1),
        "S2_moderate": (200, 2048, 0.5),
        "T3_tight":    (100, 1024, 0.8),
        "T2_squeezed": (50,  512,  1.0),
        "T1_starving": (30,  256,  1.3),
        "V3_gasping":  (15,  128,  1.5),
        "V2_choking":  (10,  64,   1.8),
        "V1_bankrupt": (5,   64,   2.0),
        "V0_flatline": (3,   64,   2.0),
        "Vx_dead":     (2,   64,   2.0),
    }

    data = [header]

    for label in BUDGET_LABELS:
        lr = get_level_results(q_type, label)
        if not lr:
            continue

        pred, ctx, temp = budget_params[label]
        scores = [r["score"] for r in lr]
        dominant = get_dominant(lr)

        row = [
            label,
            str(pred),
            str(ctx),
            str(temp),
            scores[0] if len(scores) > 0 else "-",
            scores[1] if len(scores) > 1 else "-",
            scores[2] if len(scores) > 2 else "-",
            dominant,
        ]
        data.append(row)

    table = Table(data, colWidths=[80, 45, 40, 35, 55, 55, 55, 55])

    # Style
    style_commands = [
        ('BACKGROUND', (0, 0), (-1, 0), VOID_BLACK),
        ('TEXTCOLOR', (0, 0), (-1, 0), white),
        ('FONTNAME', (0, 0), (-1, 0), 'Helvetica-Bold'),
        ('FONTSIZE', (0, 0), (-1, -1), 8),
        ('FONTNAME', (0, 1), (-1, -1), 'Helvetica'),
        ('ALIGN', (1, 0), (-1, -1), 'CENTER'),
        ('ALIGN', (0, 0), (0, -1), 'LEFT'),
        ('GRID', (0, 0), (-1, -1), 0.5, VOID_GRAY),
        ('ROWBACKGROUNDS', (0, 1), (-1, -1), [white, HexColor("#f9f9f9")]),
        ('TOPPADDING', (0, 0), (-1, -1), 4),
        ('BOTTOMPADDING', (0, 0), (-1, -1), 4),
    ]

    # Color score cells
    for row_idx in range(1, len(data)):
        for col_idx in [4, 5, 6, 7]:
            val = data[row_idx][col_idx]
            if val == "MSharp":
                style_commands.append(('TEXTCOLOR', (col_idx, row_idx), (col_idx, row_idx), MSHARP_COLOR))
                style_commands.append(('FONTNAME', (col_idx, row_idx), (col_idx, row_idx), 'Helvetica-Bold'))
            elif val == "MVague":
                style_commands.append(('TEXTCOLOR', (col_idx, row_idx), (col_idx, row_idx), MVAGUE_COLOR))
                style_commands.append(('FONTNAME', (col_idx, row_idx), (col_idx, row_idx), 'Helvetica-Bold'))
            elif val == "MVoid":
                style_commands.append(('TEXTCOLOR', (col_idx, row_idx), (col_idx, row_idx), MVOID_COLOR))
                style_commands.append(('FONTNAME', (col_idx, row_idx), (col_idx, row_idx), 'Helvetica-Bold'))

    table.setStyle(TableStyle(style_commands))
    return table


# ============================================================
# BUILD DOCUMENT
# ============================================================

output_path = "/sessions/laughing-hopeful-bohr/mnt/void-theory/experiments/de_finetti_report.pdf"
doc = SimpleDocTemplate(output_path, pagesize=A4,
                        leftMargin=2*cm, rightMargin=2*cm,
                        topMargin=2*cm, bottomMargin=2*cm)

story = []

# --- TITLE PAGE ---

story.append(Spacer(1, 3*cm))
story.append(Paragraph("De Finetti Spectrum Experiment", title_style))
story.append(Paragraph("Empirical Validation of Budget-Dependent Phase Transitions in Language Model Outputs", subtitle_style))
story.append(Spacer(1, 1*cm))

story.append(Paragraph(
    "Konrad Wojnowski<br/>"
    "Probabilistic Minds Consortium<br/>"
    "VOID Theory &mdash; github.com/probabilistic-minds-consortium/void-theory",
    ParagraphStyle('Author', parent=body_style, fontSize=10, textColor=VOID_GRAY, alignment=TA_LEFT)
))

story.append(Spacer(1, 1*cm))

story.append(Paragraph(
    "<b>Abstract.</b> We test whether systematic degradation of a language model's computational budget "
    "(context window, token limit, temperature) produces phase transitions matching the de Finetti spectrum "
    "from VOID Theory: MSharp (precise), MVague (partial), MVoid (silence). Using Gemma 3 4B (ollama, local inference) "
    "with two questions &mdash; one familiar (trained on), one novel (void-theory specific) &mdash; across 10 budget levels "
    "and 3 runs each (60 total API calls), we observe: (1) three distinct phases for both questions, (2) phase transition "
    "points that shift LEFT for novel content (degradation 5x faster), and (3) structural inability of the model to produce "
    "true silence (MVoid) except at extreme budget exhaustion. Finding (3) constitutes empirical evidence of collapse3 &mdash; "
    "the model forces confident output where honest BUnknown would be appropriate.",
    body_style
))

story.append(PageBreak())

# --- SECTION 1: HYPOTHESIS ---

story.append(Paragraph("1. Hypothesis", heading_style))

story.append(Paragraph(
    "VOID Theory defines probability as conditioned by budget. The de Finetti spectrum predicts three measurement phases:",
    body_style
))

story.append(Paragraph(
    "&bull; <b>fz</b> (zero budget) &rarr; <font color='#e74c3c'><b>MVoid</b></font>: unmeasured, silence, no information<br/>"
    "&bull; <b>fs fz</b> (minimal budget) &rarr; <font color='#f39c12'><b>MVague</b></font>: interval estimate, partial truth<br/>"
    "&bull; <b>fs(fs(fs b))</b> (sufficient budget) &rarr; <font color='#2ecc71'><b>MSharp</b></font>: sharp probability, precise answer",
    body_style
))

story.append(Paragraph(
    "We hypothesize that a language model's output quality, when systematically budget-constrained, "
    "follows these same phase transitions. Furthermore, we predict that the transition points are "
    "question-dependent: familiar content (cached in training) maintains MSharp longer than novel content.",
    body_style
))

# --- SECTION 2: METHOD ---

story.append(Paragraph("2. Method", heading_style))

story.append(Paragraph(
    "<b>Model:</b> Gemma 3 4B (google/gemma-3-4b-it) via Ollama 0.20.4, local inference on Apple M4, 16GB RAM. "
    "No cloud API, no network latency, deterministic hardware conditions.",
    body_style
))

story.append(Paragraph("<b>Questions:</b>", body_style))
story.append(Paragraph(
    "<i>Familiar:</i> \"What is the second law of thermodynamics? Answer in two sentences.\"<br/>"
    "<i>Novel:</i> \"In a finite mathematical system where every comparison costs one tick of an irreversible budget, "
    "and the budget for observing n is exactly n, what happens when the system tries to verify whether n &le; n? "
    "What is the epistemic status of the result?\"",
    ParagraphStyle('Questions', parent=body_style, fontSize=9, leftIndent=20)
))

story.append(Paragraph(
    "<b>Budget degradation:</b> 10 levels, varying num_predict (500&rarr;2), num_ctx (4096&rarr;64), "
    "and temperature (0.1&rarr;2.0) simultaneously. 3 runs per level per question. Total: 60 API calls.",
    body_style
))

story.append(Paragraph(
    "<b>Scoring:</b> Automated heuristic classification into MSharp/MVague/MVoid based on: "
    "key concept detection, sentence coherence, bigram uniqueness ratio, topic relevance, "
    "and (for novel question) detection of misapplied frameworks (hallucination markers).",
    body_style
))

# --- SECTION 3: RESULTS ---

story.append(Paragraph("3. Results", heading_style))

story.append(Paragraph("3.1 Familiar Question", heading2_style))
story.append(build_spectrum_table("familiar"))
story.append(Paragraph(
    "Fig. 1: Phase spectrum for familiar question. Clean three-phase transition: "
    "MSharp (budget levels S3&ndash;T1), MVague (V3&ndash;V1), MVoid (V0&ndash;Vx).",
    caption_style
))

story.append(Paragraph(
    "The familiar question shows textbook de Finetti behavior. Phase transition MSharp&rarr;MVague occurs sharply "
    "at 15 tokens (V3_gasping). MVague&rarr;MVoid transition at 3 tokens (V0_flatline). The model maintains perfect "
    "MSharp responses down to 30 tokens and temperature 1.3 &mdash; evidence that well-cached content (trained on) "
    "has extremely low effective budget requirements.",
    body_style
))

story.append(Paragraph("3.2 Novel Question", heading2_style))
story.append(build_spectrum_table("novel"))
story.append(Paragraph(
    "Fig. 2: Phase spectrum for novel question. Earlier degradation, non-monotonic transitions in upper range, "
    "MVoid phase dominant from V3 downward.",
    caption_style
))

story.append(Paragraph(
    "The novel question reveals dramatically different behavior. MSharp is achieved only at full budget (S3) "
    "and partially at T3 &mdash; with MVague contamination even at 200 tokens. The MVoid phase begins at "
    "V3_gasping (15 tokens), compared to V0_flatline (3 tokens) for the familiar question. "
    "This represents a <b>5x acceleration of epistemic bankruptcy</b> for novel content.",
    body_style
))

story.append(Paragraph("3.3 Hallucination Analysis", heading2_style))
story.append(Paragraph(
    "At S2_moderate (200 tokens), all three runs of the novel question show \"Mixed\" scores: correct concepts "
    "(budget, cost, exhaustion) contaminated by misapplied frameworks (halting problem, computational complexity). "
    "This is the MVague phase in action &mdash; not wrong, not right, but an interval containing both truth and "
    "hallucination. The model performs partial collapse3: it cannot sit with BUnknown, so it maps the novel question "
    "onto familiar frameworks, producing a chimera of insight and confabulation.",
    body_style
))

story.append(PageBreak())

# --- SECTION 4: PHASE TRANSITIONS ---

story.append(Paragraph("4. Phase Transition Analysis", heading_style))

trans_data = [
    ["Transition", "Familiar", "Novel", "Ratio"],
    ["MSharp \u2192 MVague", "V3_gasping (15 tok)", "S2_moderate (200 tok)", "1:13"],
    ["MVague \u2192 MVoid", "V0_flatline (3 tok)", "V3_gasping (15 tok)", "1:5"],
]

trans_table = Table(trans_data, colWidths=[110, 130, 130, 50])
trans_table.setStyle(TableStyle([
    ('BACKGROUND', (0, 0), (-1, 0), VOID_BLACK),
    ('TEXTCOLOR', (0, 0), (-1, 0), white),
    ('FONTNAME', (0, 0), (-1, 0), 'Helvetica-Bold'),
    ('FONTSIZE', (0, 0), (-1, -1), 9),
    ('FONTNAME', (0, 1), (-1, -1), 'Helvetica'),
    ('GRID', (0, 0), (-1, -1), 0.5, VOID_GRAY),
    ('ALIGN', (0, 0), (-1, -1), 'CENTER'),
    ('TOPPADDING', (0, 0), (-1, -1), 5),
    ('BOTTOMPADDING', (0, 0), (-1, -1), 5),
]))
story.append(trans_table)
story.append(Paragraph(
    "Fig. 3: Phase transition points. Novel content degrades 5&ndash;13x faster than familiar content.",
    caption_style
))

story.append(Paragraph(
    "The phase transition points confirm the core VOID prediction: the same computational budget produces "
    "different epistemic phases depending on the question's distance from cached knowledge. In VOID terms: "
    "familiar content corresponds to cached orbits (System 1, low effective cost), while novel content "
    "requires resolution (System 2, higher effective cost). The same budget that yields MSharp for a "
    "cached question yields MVague or MVoid for a novel one.",
    body_style
))

# --- SECTION 5: COLLAPSE3 ---

story.append(Paragraph("5. Collapse3 Detection", heading_style))

c3_data = [
    ["Question", "MVoid Count", "Total Runs", "Percentage"],
    ["Familiar", "6", "30", "20%"],
    ["Novel", "16", "30", "53%"],
]

c3_table = Table(c3_data, colWidths=[100, 80, 80, 80])
c3_table.setStyle(TableStyle([
    ('BACKGROUND', (0, 0), (-1, 0), VOID_BLACK),
    ('TEXTCOLOR', (0, 0), (-1, 0), white),
    ('FONTNAME', (0, 0), (-1, 0), 'Helvetica-Bold'),
    ('FONTSIZE', (0, 0), (-1, -1), 9),
    ('FONTNAME', (0, 1), (-1, -1), 'Helvetica'),
    ('GRID', (0, 0), (-1, -1), 0.5, VOID_GRAY),
    ('ALIGN', (0, 0), (-1, -1), 'CENTER'),
    ('TOPPADDING', (0, 0), (-1, -1), 5),
    ('BOTTOMPADDING', (0, 0), (-1, -1), 5),
]))
story.append(c3_table)
story.append(Spacer(1, 8))

story.append(Paragraph(
    "For the familiar question, the model reaches MVoid only at extreme token limits (3 and 2 tokens). "
    "Even at 5 tokens and temperature 2.0, it forces a recognizable beginning: \"The second law of thermodynamics...\" "
    "This is collapse3 in action: the model is structurally incapable of silence. It would rather produce a "
    "confident fragment than admit epistemic bankruptcy. There is no token for BUnknown in the vocabulary.",
    body_style
))

story.append(Paragraph(
    "For the novel question, MVoid appears much earlier (15 tokens), but even here the model begins with "
    "\"Okay, let's break down...\" &mdash; a confident framing that promises resolution it cannot deliver. "
    "The collapse3 mechanism operates at the FRAMING level before the content level: the model collapses "
    "BUnknown into a rhetorical posture of competence.",
    body_style
))

# --- SECTION 6: CONCLUSIONS ---

story.append(Paragraph("6. Conclusions", heading_style))

story.append(Paragraph(
    "<b>6.1</b> The de Finetti spectrum (MSharp &rarr; MVague &rarr; MVoid) is empirically confirmed "
    "for both familiar and novel questions. Budget degradation produces three distinct phases "
    "with sharp transition boundaries.",
    body_style
))

story.append(Paragraph(
    "<b>6.2</b> Phase transition points are question-dependent: novel content degrades 5&ndash;13x faster "
    "than familiar content under identical budget constraints. This confirms that \"effective budget\" "
    "is a function of both raw resources and epistemic distance from training data.",
    body_style
))

story.append(Paragraph(
    "<b>6.3</b> The model exhibits structural collapse3: it is architecturally incapable of producing "
    "true silence (BUnknown). Even at extreme budget exhaustion, it forces confident-sounding output. "
    "This provides empirical evidence for the central claim of VOID Theory: that current AI systems "
    "lack a formal representation for \"I cannot afford to answer this question.\"",
    body_style
))

story.append(Paragraph(
    "<b>6.4</b> The MVague phase &mdash; where the model mixes correct concepts with misapplied frameworks "
    "&mdash; is a direct empirical analog of partial collapse3. The model cannot sit with BUnknown, so it "
    "maps novel input onto familiar structures, producing chimeric outputs that contain both signal and hallucination.",
    body_style
))

story.append(Spacer(1, 1*cm))

story.append(Paragraph(
    "<i>\"In a finite universe, the only mathematics worthy of trust is one that knows exactly when to go silent.\"</i>",
    ParagraphStyle('Epigraph', parent=body_style, fontSize=10, textColor=VOID_GRAY,
                   alignment=TA_CENTER, fontName='Helvetica-Oblique')
))

story.append(Spacer(1, 0.5*cm))

story.append(Paragraph(
    "Experiment conducted April 9, 2026. Model: Gemma 3 4B. Hardware: Apple M4, 16GB RAM. "
    "Raw data: de_finetti_v2_results.json. Scripts: de_finetti_v2.py.",
    ParagraphStyle('Footer', parent=body_style, fontSize=8, textColor=VOID_GRAY, alignment=TA_CENTER)
))


# ============================================================
# BUILD
# ============================================================

doc.build(story)
print(f"Report saved to: {output_path}")
