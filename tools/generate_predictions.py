#!/usr/bin/env python3
"""
Generate the predictions summary table in three formats (LaTeX, HTML, Markdown)
from a single data source. Run before LaTeX compilation.

Outputs:
  src/generated/predictions-table.tex  — \\input'd by the cover sheet
  index.html                           — injected between markers
  README.md                            — injected between markers

Tokens in curly braces (e.g. {Omega_Lambda}) are looked up in SYMBOLS
and rendered per format. Everything else passes through as plain text.
"""

import os
import re

REPO_ROOT = os.path.join(os.path.dirname(__file__), '..')

# ─── Symbol dictionary: token → (markdown, html, latex) ─────────────────────

SYMBOLS = {
    # Density parameters
    'Omega_Lambda': ('Ω_Λ', '&Omega;<sub>&Lambda;</sub>',
                     r'$\Omega_\Lambda$'),
    'Omega_m': ('Ω_m', '&Omega;<sub>m</sub>', r'$\Omega_m$'),
    'Omega_r': ('Ω_r', '&Omega;<sub>r</sub>', r'$\Omega_r$'),
    'Omega_b': ('Ω_b', '&Omega;<sub>b</sub>', r'$\Omega_b$'),
    # Particle masses
    'm_tau': ('m_τ', '<em>m</em><sub>&tau;</sub>', r'$m_\tau$'),
    'm_mu': ('m_μ', '<em>m</em><sub>&mu;</sub>', r'$m_\mu$'),
    'm_e': ('m_e', '<em>m</em><sub>e</sub>', r'$m_e$'),
    'm_H': ('m_H', '<em>m</em><sub>H</sub>', r'$m_H$'),
    'm_W': ('m_W', '<em>m</em><sub>W</sub>', r'$m_W$'),
    'M_Z': ('M_Z', '<em>M</em><sub>Z</sub>', r'$M_Z$'),
    # Coupling constants and angles
    'alpha_s': ('α_s', '&alpha;<sub>s</sub>', r'$\alpha_s$'),
    'alpha': ('α', '&alpha;', r'$\alpha$'),
    'sin2_theta_W': ('sin²θ_W', 'sin<sup>2</sup>&theta;<sub>W</sub>',
                     r'$\sin^2\theta_W$'),
    'theta_C': ('θ_C', '&theta;<sub>C</sub>', r'$\theta_C$'),
    'theta_QCD': ('θ_QCD', '&theta;<sub>QCD</sub>',
                  r'$\theta_{\mathrm{QCD}}$'),
    'chi': ('χ', '&chi;', r'$\chi$'),
    'sigma': ('σ', '&sigma;', r'$\sigma$'),
    # Cosmological
    'H_0': ('H₀', '<em>H</em><sub>0</sub>', r'$H_0$'),
    'r_d': ('r_d', '<em>r</em><sub>d</sub>', r'$r_d$'),
    'T_CMB': ('T_CMB', '<em>T</em><sub>CMB</sub>',
              r'$T_{\mathrm{CMB}}$'),
    'n_s': ('n_s', '<em>n</em><sub>s</sub>', r'$n_s$'),
    'A_s': ('A_s', '<em>A</em><sub>s</sub>', r'$A_s$'),
    'ell_A': ('ℓ_A', '&ell;<sub>A</sub>', r'$\ell_A$'),
    # Greek and math
    'pi': ('π', '&pi;', r'$\pi$'),
    'Delta_Phi': ('ΔΦ', '&Delta;&Phi;', r'$\Delta\Phi$'),
    'delta_Phi': ('δΦ', '&delta;&Phi;', r'$\delta\Phi$'),
    'sqrt_pi': ('√π', '&radic;&pi;', r'$\sqrt{\pi}$'),
    # Topology
    'pi3_S11': ('π₃(S¹¹)', '&pi;<sub>3</sub>(S<sup>11</sup>)',
                r'$\pi_3(S^{11})$'),
    'Z2': ('Z₂', 'Z<sub>2</sub>', r'$\mathbb{Z}_2$'),
    'S3': ('S³', 'S<sup>3</sup>', r'$S^3$'),
    'd1_19': ('d₁=19', '<em>d</em><sub>1</sub>=19', r'$d_1\!=\!19$'),
    # Compound math (exponent inside math mode)
    'pi7': ('π⁷', '&pi;<sup>7</sup>', r'$\pi^7$'),
    'pi2': ('π²', '&pi;<sup>2</sup>', r'$\pi^2$'),
    'chi_k': ('χ^k', '&chi;<sup>k</sup>', r'$\chi^k$'),
    'chi3': ('χ³', '&chi;<sup>3</sup>', r'$\chi^3$'),
    'chi2': ('χ²', '&chi;<sup>2</sup>', r'$\chi^2$'),
    'chi2_n': ('χ²/n', '&chi;<sup>2</sup>/n', r'$\chi^2/n$'),
    # Formatting
    'times': ('×', '&times;', r'$\times$'),
    'pm': ('±', '&plusmn;', r'$\pm$'),
    'cap': ('∩', '&cap;', r'$\cap$'),
    'cdot': ('·', '&middot;', r'$\cdot$'),
    'neq': ('≠', '&ne;', r'$\neq$'),
    'approx': ('≈', '&approx;', r'$\approx$'),
    'deg': ('°', '&deg;', r'$^\circ$'),
    'mdash': ('—', '&mdash;', '---'),
    'minus': ('−', '&minus;', '$-$'),
    'pct': ('%', '%', r'\%'),
    'chi2': ('χ²', '&chi;<sup>2</sup>', r'$\chi^2$'),
    'sup_minus120': ('⁻¹²⁰', '<sup>&minus;120</sup>', r'$^{-120}$'),
    'sup_minus5': ('⁻⁵', '<sup>&minus;5</sup>', r'$^{-5}$'),
    'ldquo': ('\u201c', '&ldquo;', "``"),
    'rdquo': ('\u201d', '&rdquo;', "''"),
}


def render(text, fmt):
    """Replace {token} placeholders with format-specific strings."""
    idx = {'md': 0, 'html': 1, 'latex': 2}[fmt]

    def replace_token(match):
        token = match.group(1)
        if token in SYMBOLS:
            return SYMBOLS[token][idx]
        return match.group(0)  # leave unknown tokens unchanged

    return re.sub(r'\{(\w+)\}', replace_token, text)


def latex_escape(text):
    """Escape LaTeX special chars in rendered text."""
    # Only escape chars that aren't inside $ delimiters
    parts = text.split('$')
    for i in range(0, len(parts), 2):  # even indices are outside math
        parts[i] = parts[i].replace('#', r'\#')
    return '$'.join(parts)


# ─── Single source of truth ──────────────────────────────────────────────────

INTRO = ("One hypothesis. Zero free parameters. "
         "Every prediction below is a test of the hypothesis.")

TIERS = [
    {
        'number': 1,
        'title': 'Exact: Forced by Uniqueness Theorems',
        'description': ('Mathematical uniqueness proofs leave no alternative. '
                        'These are not approximations.'),
        'columns': ['Prediction', 'Value', 'Status', 'Source'],
        'rows': [
            ['Spacetime dimension', 'd = 4',
             'Confirmed', 'Lovelock {cap} Clifford (III)'],
            ['Metric signature', '({minus},+,+,+)',
             'Confirmed', 'Propagator + Clifford (III)'],
            ['Gauge group', 'SU(3) {times} SU(2) {times} U(1)',
             'Confirmed', 'Adams + Bott (IVa)'],
            ['Symmetry breaking', 'SU(2) broken; SU(3), U(1) exact',
             'Confirmed', 'Hairy ball theorem (IVa)'],
            ['Fermion generations', 'Exactly 3',
             'Confirmed', 'Bott periodicity + {d1_19} (IVa)'],
            ['Cosmological constant', '1.099 {times} 10{sup_minus120}',
             '0.1{pct} match', 'Cascade invariant (I)'],
            ['Dark energy EoS', 'w = {minus}1 exactly',
             'Confirmed', 'Fixed geometric constant (III)'],
            ['Strong CP phase', '{theta_QCD} = 0',
             'Confirmed', '{pi3_S11} = {Z2} (IVa)'],
            ['No supersymmetry', '{mdash}',
             'Confirmed (LHC)', 'No pairing mechanism (IVa)'],
            ['No dark matter particles', '{mdash}',
             'Confirmed (null results)', 'Geometry provides content (V)'],
            ['No extra Higgs bosons', '{mdash}',
             'Confirmed (LHC)', 'One hairy ball zero (IVa)'],
        ],
    },
    {
        'number': 2,
        'title': 'Derived: Closed-Form, Zero Free Parameters',
        'description': ('Numerical predictions from cascade geometry. '
                        'Formulas are exact; deviations reflect '
                        'leading-order truncation.'),
        'columns': ['Observable', 'Formula', 'Predicted', 'Observed', 'Dev.'],
        'rows': [
            ['{Omega_Lambda}', '({pi}{minus}1)/{pi}',
             '0.6817', '0.685 {pm} 0.007', '{minus}0.5{pct}'],
            ['{Omega_m}', '1/{pi}',
             '0.3183', '0.315 {pm} 0.007', '+1.1{pct}'],
            ['{Omega_r}', '1/(4{pi7})',
             '8.28 {times} 10{sup_minus5}',
             '8.27 {times} 10{sup_minus5}', '+0.1{pct}'],
            ['{T_CMB}', 'from {Omega_r}',
             '2.730 K', '2.7255 K', '+0.16{pct}'],
            ['{m_H} / {m_W}', '{pi}/2',
             '1.5708', '1.559', '+0.8{pct}'],
            ['{m_mu} / {m_e}', 'exp({Delta_Phi}) {cdot} 2{sqrt_pi}',
             '206.50', '206.77', '+0.13{pct}'],
            ['{m_e}', 'geometric-topological',
             '0.514 MeV', '0.511 MeV', '+0.6{pct}'],
            ['{m_mu}', 'geometric-topological',
             '106.2 MeV', '105.66 MeV', '+0.5{pct}'],
            ['{alpha_s}({M_Z}) leading', '{alpha}(12) {cdot} exp({Delta_Phi})',
             '0.1159', '0.1179 {pm} 0.0009', '{minus}1.7{pct}'],
            ['{sin2_theta_W} leading', 'Radon-Hurwitz ratio',
             '0.2286', '0.23121', '{minus}1.1{pct}'],
        ],
    },
    {
        'number': 3,
        'title': 'Precision: Correction-Family Closures',
        'description': ('Seven observables close within experimental error '
                        'via {delta_Phi} = {alpha}(d*)/{chi_k} shifts sourced '
                        "at Part 0's distinguished dimensions. Three "
                        'shift-observable pairs reuse the same correction '
                        'across independent quantities.'),
        'columns': ['Observable', 'Shift source', 'Predicted', 'Observed',
                    'Residual'],
        'rows': [
            ['{alpha_s}({M_Z})', '{alpha}(14)/{chi}',
             '0.11792', '0.1179 {pm} 0.0009', '+0.02{sigma}'],
            ['{m_tau} / {m_mu}', '{alpha}(14)/{chi}',
             '16.8173', '16.8170 {pm} 0.0011', '+0.24{sigma}'],
            ['{m_tau} absolute', '{alpha}(19)/{chi}',
             '1776.82 MeV', '1776.86 {pm} 0.12', '{minus}0.31{sigma}'],
            ['{sin2_theta_W}', '{alpha}(5)/{chi3}',
             '0.23123', '0.23121 {pm} 0.00004', '+0.40{sigma}'],
            ['{Omega_m}', '{minus}{alpha}(5)/{chi3}',
             '0.31474', '0.315 {pm} 0.007', '{minus}0.04{sigma}'],
            ['{theta_C} (Cabibbo)', '{minus}{alpha}(7)/{chi2}',
             '13.04{deg}', '13.04 {pm} 0.05{deg}', '+0.03{sigma}'],
        ],
    },
    {
        'number': 4,
        'title': 'Frontier: Under Active Experimental Test',
        'description': ('Specific predictions testable by current or '
                        'near-future experiments (DESI, Euclid, CMB-S4, '
                        'SH0ES).'),
        'columns': ['Observable', 'Predicted', 'Current data', 'Status'],
        'rows': [
            ['{H_0}', '71.05 km/s/Mpc',
             'Planck: 67.4 {cdot} SH0ES: 73.0',
             'Between tensions; resolves with cascade {r_d}'],
            ['{r_d} (sound horizon)', '{approx}141 Mpc',
             'Planck: 147.6 Mpc',
             'DESI BAO: cascade fits better ({chi2_n} = 1.70 vs 1.90)'],
            ['DESI w {neq} {minus}1 signal',
             'w = {minus}1; apparent deviation is ruler mismatch',
             'DESI DR2: w {approx} {minus}0.76',
             'Cascade explains signal without dynamical dark energy'],
        ],
    },
    {
        'number': 5,
        'title': 'Provisional: Derivation Incomplete',
        'description': ('Results where the argument has acknowledged gaps '
                        'or needs strengthening.'),
        'columns': ['Observable', 'Issue'],
        'rows': [
            ['{Omega_b} = 1/(2{pi2})',
             '{ldquo}One unit of content on {S3}{rdquo} argument needs strengthening'],
            ['{n_s}, {A_s}',
             'Primordial spectrum not yet derived'],
            ['Correction selection rule',
             'Observable-to-source assignment not fully derived '
             'from first principles'],
        ],
    },
]


# ─── Markdown output ────────────────────────────────────────────────────────

def generate_markdown():
    lines = ['## Predictions', '', INTRO, '']
    for tier in TIERS:
        lines.append(
            f"### Tier {tier['number']} \u2014 "
            f"{render(tier['title'], 'md')}"
        )
        lines.append('')
        lines.append(render(tier['description'], 'md'))
        lines.append('')
        cols = tier['columns']
        lines.append('| ' + ' | '.join(cols) + ' |')
        lines.append('|' + '|'.join(['---'] * len(cols)) + '|')
        for row in tier['rows']:
            cells = [render(c, 'md') for c in row]
            lines.append('| ' + ' | '.join(cells) + ' |')
        lines.append('')
    return '\n'.join(lines)


# ─── HTML output ─────────────────────────────────────────────────────────────

def generate_html():
    parts = [
        '  <h2>Predictions</h2>',
        f'  <p style="margin-bottom:0.5rem;">{INTRO}</p>',
    ]
    for tier in TIERS:
        parts.append('')
        parts.append(
            f'  <h3 style="font-size:1.1rem; margin-top:1.5rem; '
            f'color:var(--accent);">Tier {tier["number"]} &mdash; '
            f'{render(tier["title"], "html")}</h3>'
        )
        parts.append(
            f'  <p style="font-size:0.9rem; color:var(--muted); '
            f'margin-bottom:0.75rem;">'
            f'{render(tier["description"], "html")}</p>'
        )
        parts.append(
            '  <table style="width:100%; border-collapse:collapse; '
            'font-size:0.9rem; margin-bottom:1.5rem;">'
        )
        # Header
        ths = ''.join(
            f'<th style="padding:0.4rem 0.6rem;">{c}</th>'
            for c in tier['columns']
        )
        parts.append(
            f'    <tr style="border-bottom:2px solid var(--border); '
            f'text-align:left;">{ths}</tr>'
        )
        # Rows
        for row in tier['rows']:
            tds = ''.join(
                f'<td style="padding:0.4rem 0.6rem;">'
                f'{render(c, "html")}</td>'
                for c in row
            )
            parts.append(
                f'    <tr style="border-bottom:1px solid var(--border);">'
                f'{tds}</tr>'
            )
        parts.append('  </table>')
    return '\n'.join(parts)


# ─── LaTeX output ────────────────────────────────────────────────────────────

def generate_latex():
    lines = [
        '% Auto-generated by tools/generate_predictions.py',
        '% Do not edit manually; edit the data in generate_predictions.py',
        '',
        r'\section*{Predictions}',
        '',
        r'\noindent ' + INTRO,
        '',
    ]
    # Column specs per tier type (by column count)
    colspecs = {
        2: (r'@{}>{\raggedright}p{3.5cm} '
            r'>{\raggedright\arraybackslash}p{9.5cm}@{}'),
        4: (r'@{}>{\raggedright}p{3.2cm} p{4.2cm} l '
            r'>{\raggedright\arraybackslash}p{4cm}@{}'),
        5: r'@{}lllrr@{}',
    }

    for tier in TIERS:
        lines.append(r'\subsection*{Tier %d --- %s}' % (
            tier['number'], render(tier['title'], 'latex'),
        ))
        lines.append('')
        lines.append(
            r'\noindent ' + render(tier['description'], 'latex')
        )
        lines.append(r'\smallskip')

        ncols = len(tier['columns'])
        spec = colspecs.get(ncols, '@{}' + 'l' * ncols + '@{}')
        lines.append(r'\begin{tabular}{%s}' % spec)
        lines.append(r'\toprule')
        lines.append(' & '.join(tier['columns']) + r' \\')
        lines.append(r'\midrule')
        for row in tier['rows']:
            cells = [latex_escape(render(c, 'latex')) for c in row]
            lines.append(' & '.join(cells) + r' \\')
        lines.append(r'\bottomrule')
        lines.append(r'\end{tabular}')
        lines.append('')
    return '\n'.join(lines)


# ─── File injection ──────────────────────────────────────────────────────────

BEGIN = '<!-- BEGIN PREDICTIONS -->'
END = '<!-- END PREDICTIONS -->'


def inject(filepath, content):
    """Replace content between markers in a file."""
    with open(filepath, 'r') as f:
        text = f.read()
    if BEGIN not in text or END not in text:
        raise ValueError(f"Markers not found in {filepath}")
    pattern = re.escape(BEGIN) + r'.*?' + re.escape(END)
    replacement = BEGIN + '\n' + content + '\n' + END
    with open(filepath, 'w') as f:
        f.write(re.sub(pattern, replacement, text, flags=re.DOTALL))


# ─── Main ───────────────────────────────────────────────────────────────────

def main():
    out_dir = os.path.join(REPO_ROOT, 'src', 'generated')
    os.makedirs(out_dir, exist_ok=True)

    # LaTeX fragment
    latex_path = os.path.join(out_dir, 'predictions-table.tex')
    with open(latex_path, 'w') as f:
        f.write(generate_latex())
    print(f"  wrote {latex_path}")

    # HTML injection
    inject(os.path.join(REPO_ROOT, 'index.html'), generate_html())
    print("  injected predictions into index.html")

    # Markdown injection
    inject(os.path.join(REPO_ROOT, 'README.md'), generate_markdown())
    print("  injected predictions into README.md")

    total = sum(len(t['rows']) for t in TIERS)
    print(f"\n  {len(TIERS)} tiers, {total} predictions, 3 formats.")


if __name__ == '__main__':
    main()
