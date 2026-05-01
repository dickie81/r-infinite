#!/usr/bin/env python3
"""
Generate the predictions table for index.html and the LaTeX cover sheet
by reading the canonical source from PREDICTIONS.md.

PREDICTIONS.md is the single source of truth. This script:
  1. Parses the '## Predictions' section from PREDICTIONS.md
  2. Converts to HTML (injected into index.html between markers)
  3. Converts to LaTeX (written to src/generated/predictions-table.tex)

The main README.md shows only a compact headline subset; editing README.md
does not affect the LaTeX/HTML output. To add or update a prediction: edit
PREDICTIONS.md, then run this script. CI runs it automatically before every
build.

PREDICTIONS.md does not use BEGIN/END markers because it is a dedicated file
— the parser locates the predictions section via the '## Predictions' header
and reads to end-of-file. Markers are still used in web/index.html where the
generated HTML is injected alongside other page content.
"""

import os
import re

REPO_ROOT = os.path.join(os.path.dirname(__file__), '..', '..')

# Markers used only for HTML injection into web/index.html. The source file
# PREDICTIONS.md does not use markers — the parser locates the section by
# its '## Predictions' header.
BEGIN = '<!-- BEGIN PREDICTIONS -->'
END = '<!-- END PREDICTIONS -->'

# ─── Term conversion table ───────────────────────────────────────────────────
# Each entry: (markdown_text, html_text, latex_text)
# Applied longest-first to avoid partial matches.

TERMS = [
    # Compound terms (longest first to prevent partial matches)
    ('sin²θ_W', 'sin<sup>2</sup>&theta;<sub>W</sub>',
     r'$\sin^2\theta_W$'),
    ('θ_QCD', '&theta;<sub>QCD</sub>',
     r'$\theta_{\mathrm{QCD}}$'),
    ('π₃(S¹¹)', '&pi;<sub>3</sub>(S<sup>11</sup>)',
     r'$\pi_3(S^{11})$'),
    ('10⁻¹²⁰', '10<sup>&minus;120</sup>', r'$10^{-120}$'),
    ('10⁻¹²¹', '10<sup>&minus;121</sup>', r'$10^{-121}$'),
    ('10⁻⁵', '10<sup>&minus;5</sup>', r'$10^{-5}$'),
    ('10⁻⁴', '10<sup>&minus;4</sup>', r'$10^{-4}$'),
    ('10⁻⁶', '10<sup>&minus;6</sup>', r'$10^{-6}$'),
    ('√Δm²_atm', '&radic;&Delta;<em>m</em><sup>2</sup><sub>atm</sub>',
     r'$\sqrt{\Delta m^2_{\mathrm{atm}}}$'),
    ('Δm²_atm', '&Delta;<em>m</em><sup>2</sup><sub>atm</sub>',
     r'$\Delta m^2_{\mathrm{atm}}$'),
    ('Δm²', '&Delta;<em>m</em><sup>2</sup>', r'$\Delta m^2$'),
    ('M⁴_Pl,red', '<em>M</em><sup>4</sup><sub>Pl,red</sub>',
     r'$M^{4}_{\mathrm{Pl,red}}$'),
    ('ρ_Λ', '&rho;<sub>&Lambda;</sub>', r'$\rho_\Lambda$'),
    ('Ω(19)', '&Omega;<sub>19</sub>', r'$\Omega_{19}$'),
    ('Ω(217)', '&Omega;<sub>217</sub>', r'$\Omega_{217}$'),
    ('ΛCDM', '&Lambda;CDM', r'$\Lambda$CDM'),
    ('t₀', '<em>t</em><sub>0</sub>', r'$t_0$'),
    ('T_CMB', '<em>T</em><sub>CMB</sub>',
     r'$T_{\mathrm{CMB}}$'),
    ('α_s', '&alpha;<sub>s</sub>', r'$\alpha_s$'),
    ('Ω_Λ', '&Omega;<sub>&Lambda;</sub>', r'$\Omega_\Lambda$'),
    ('Ω_m', '&Omega;<sub>m</sub>', r'$\Omega_m$'),
    ('Ω_r', '&Omega;<sub>r</sub>', r'$\Omega_r$'),
    ('Ω_b', '&Omega;<sub>b</sub>', r'$\Omega_b$'),
    ('θ_C', '&theta;<sub>C</sub>', r'$\theta_C$'),
    ('m_τ', '<em>m</em><sub>&tau;</sub>', r'$m_\tau$'),
    ('m_μ', '<em>m</em><sub>&mu;</sub>', r'$m_\mu$'),
    ('m_H', '<em>m</em><sub>H</sub>', r'$m_H$'),
    ('m_W', '<em>m</em><sub>W</sub>', r'$m_W$'),
    ('m_e', '<em>m</em><sub>e</sub>', r'$m_e$'),
    ('m_ν', '<em>m</em><sub>&nu;</sub>', r'$m_\nu$'),
    ('m_29', '<em>m</em><sub>29</sub>', r'$m_{29}$'),
    ('m_2', '<em>m</em><sub>2</sub>', r'$m_2$'),
    ('m_3', '<em>m</em><sub>3</sub>', r'$m_3$'),
    ('M_Z', '<em>M</em><sub>Z</sub>', r'$M_Z$'),
    ('n_s', '<em>n</em><sub>s</sub>', r'$n_s$'),
    ('A_s', '<em>A</em><sub>s</sub>', r'$A_s$'),
    ('r_d', '<em>r</em><sub>d</sub>', r'$r_d$'),
    ('d₁', '<em>d</em><sub>1</sub>', r'$d_1$'),
    ('H₀', '<em>H</em><sub>0</sub>', r'$H_0$'),
    ('Z₂', 'Z<sub>2</sub>', r'$\mathbb{Z}_2$'),
    ('S³', 'S<sup>3</sup>', r'$S^3$'),
    ('S¹¹', 'S<sup>11</sup>', r'$S^{11}$'),
    ('ΔΦ', '&Delta;&Phi;', r'$\Delta\Phi$'),
    ('δΦ', '&delta;&Phi;', r'$\delta\Phi$'),
    ('√π', '&radic;&pi;', r'$\sqrt{\pi}$'),
    ('π²', '&pi;<sup>2</sup>', r'$\pi^2$'),
    ('π³', '&pi;<sup>3</sup>', r'$\pi^3$'),
    ('π⁷', '&pi;<sup>7</sup>', r'$\pi^7$'),
    ('χ²', '&chi;<sup>2</sup>', r'$\chi^2$'),
    ('χ³', '&chi;<sup>3</sup>', r'$\chi^3$'),
    ('χ⁴', '&chi;<sup>4</sup>', r'$\chi^4$'),
    ('χ⁸', '&chi;<sup>8</sup>', r'$\chi^8$'),
    ('χ^k', '&chi;<sup>k</sup>', r'$\chi^k$'),
    # Single characters (applied after compounds)
    ('×', '&times;', r'$\times$'),
    ('±', '&plusmn;', r'$\pm$'),
    ('≈', '&approx;', r'$\approx$'),
    ('≠', '&ne;', r'$\neq$'),
    ('∩', '&cap;', r'$\cap$'),
    ('·', '&middot;', r'$\cdot$'),
    ('°', '&deg;', r'$^\circ$'),
    ('σ', '&sigma;', r'$\sigma$'),
    ('α', '&alpha;', r'$\alpha$'),
    ('χ', '&chi;', r'$\chi$'),
    ('π', '&pi;', r'$\pi$'),
    ('θ', '&theta;', r'$\theta$'),
    ('−', '&minus;', r'$-$'),
    ('—', '&mdash;', '---'),
]

# Sort by length (longest first) to prevent partial matches
TERMS.sort(key=lambda t: -len(t[0]))


def convert(text, fmt):
    """Convert markdown text to html or latex."""
    idx = {'html': 1, 'latex': 2}[fmt]
    result = text
    for md, html, latex in TERMS:
        result = result.replace(md, (html, latex)[idx - 1])
    if fmt == 'latex':
        result = result.replace('%', r'\%')
        result = result.replace('"', "''")
    return result


# ─── Parser ──────────────────────────────────────────────────────────────────

def parse_readme():
    """Parse the predictions section from PREDICTIONS.md.

    The predictions section starts at '## Predictions' and continues to
    end-of-file. No BEGIN/END markers are required in the source file.
    """
    path = os.path.join(REPO_ROOT, 'PREDICTIONS.md')
    with open(path, 'r') as f:
        text = f.read()

    match = re.search(r'## Predictions\s*\n(.*)', text, re.DOTALL)
    if not match:
        raise ValueError(
            f"'## Predictions' section header not found in {path}"
        )

    # Reconstruct section with its heading; downstream parser expects
    # a blank line after the heading (matches GitHub-rendered markdown).
    section = '## Predictions\n\n' + match.group(1).strip()

    # Extract intro (text before first ### heading)
    intro_match = re.match(r'## Predictions\s*\n\n(.+?)\n\n###', section,
                           re.DOTALL)
    intro = intro_match.group(1).strip() if intro_match else ''

    # Split into tier blocks by ### headings
    tier_blocks = re.split(r'(?=### Tier \d)', section)
    tiers = []
    for block in tier_blocks:
        m = re.match(
            r'### Tier (\d+)\s*[—–-]\s*(.+?)\n\n'
            r'(.+?)\n\n'
            r'(\|.+)',
            block.strip(), re.DOTALL,
        )
        if not m:
            continue

        number = int(m.group(1))
        title = m.group(2).strip()
        description = m.group(3).strip()
        table_text = m.group(4).strip()

        # Parse markdown table
        lines = [l for l in table_text.split('\n') if l.strip()]
        columns = [c.strip() for c in lines[0].split('|')[1:-1]]
        # Skip separator line (lines[1])
        rows = []
        for line in lines[2:]:
            cells = [c.strip() for c in line.split('|')[1:-1]]
            if cells:
                rows.append(cells)

        tiers.append({
            'number': number,
            'title': title,
            'description': description,
            'columns': columns,
            'rows': rows,
        })

    return intro, tiers


# ─── HTML generator ──────────────────────────────────────────────────────────

def generate_html(intro, tiers):
    parts = [
        '  <h2>Predictions</h2>',
        f'  <p style="margin-bottom:0.5rem;">{intro}</p>',
    ]
    for tier in tiers:
        parts.append('')
        parts.append(
            f'  <h3 style="font-size:1.1rem; margin-top:1.5rem; '
            f'color:var(--accent);">Tier {tier["number"]} &mdash; '
            f'{convert(tier["title"], "html")}</h3>'
        )
        parts.append(
            f'  <p style="font-size:0.9rem; color:var(--muted); '
            f'margin-bottom:0.75rem;">'
            f'{convert(tier["description"], "html")}</p>'
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
                f'{convert(c, "html")}</td>'
                for c in row
            )
            parts.append(
                f'    <tr style="border-bottom:1px solid var(--border);">'
                f'{tds}</tr>'
            )
        parts.append('  </table>')
    return '\n'.join(parts)


# ─── LaTeX generator ─────────────────────────────────────────────────────────

def generate_latex(intro, tiers):
    colspecs = {
        2: (r'@{}>{\raggedright}p{3.5cm} '
            r'>{\raggedright\arraybackslash}p{9.5cm}@{}'),
        4: (r'@{}>{\raggedright}p{3.2cm} p{4.2cm} l '
            r'>{\raggedright\arraybackslash}p{4cm}@{}'),
        5: r'@{}lllrr@{}',
    }
    lines = [
        '% Auto-generated by tools/generate_predictions.py from README.md',
        '% Do not edit manually; edit the predictions section in README.md',
        '',
        r'\section*{Predictions}',
        '',
        r'\noindent ' + intro,
        '',
    ]
    for tier in tiers:
        lines.append(r'\subsection*{Tier %d --- %s}' % (
            tier['number'], convert(tier['title'], 'latex'),
        ))
        lines.append('')
        lines.append(
            r'\noindent ' + convert(tier['description'], 'latex')
        )
        lines.append('')
        lines.append(r'\smallskip')
        lines.append('')
        lines.append(r'\noindent')

        ncols = len(tier['columns'])
        spec = colspecs.get(ncols, '@{}' + 'l' * ncols + '@{}')
        wrap = ncols in (4, 5)
        if wrap:
            lines.append(r'\resizebox{\textwidth}{!}{%')
        lines.append(r'\begin{tabular}{%s}' % spec)
        lines.append(r'\toprule')
        lines.append(' & '.join(tier['columns']) + r' \\')
        lines.append(r'\midrule')
        for row in tier['rows']:
            cells = [convert(c, 'latex') for c in row]
            lines.append(' & '.join(cells) + r' \\')
        lines.append(r'\bottomrule')
        lines.append(r'\end{tabular}')
        if wrap:
            lines.append(r'}')
        lines.append('')
    return '\n'.join(lines)


# ─── File injection ──────────────────────────────────────────────────────────

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
    intro, tiers = parse_readme()
    total = sum(len(t['rows']) for t in tiers)
    print(f"  Parsed PREDICTIONS.md: {len(tiers)} tiers, {total} predictions")

    # LaTeX fragment
    out_dir = os.path.join(REPO_ROOT, 'src', 'generated')
    os.makedirs(out_dir, exist_ok=True)
    latex_path = os.path.join(out_dir, 'predictions-table.tex')
    with open(latex_path, 'w') as f:
        f.write(generate_latex(intro, tiers))
    print(f"  wrote {latex_path}")

    # HTML injection
    html_path = os.path.join(REPO_ROOT, 'web/index.html')
    inject(html_path, generate_html(intro, tiers))
    print(f"  injected into {html_path}")


if __name__ == '__main__':
    main()
