#!/usr/bin/env python3
"""Generate the cascade logo SVG (web/assets/logo.svg).

The logo depicts an infinite tunnel of nested unit-ball silhouettes descending
through the cascade dimensions. Each ring layer is a scaled copy of a
square-plus-inscribed-circle glyph, animated from scale 0 (emerging from the
cascade invariant terminus) through the true cascade ratios Omega_d / Omega_7
for d = 1..7, then extrapolated off-canvas.

Every visual parameter is tunable via command-line flags. Run with --help for
the full list. The script is self-contained (only the standard library) and
writes the SVG to web/assets/logo.svg by default.

Cascade ratios Omega_d/Omega_7 for d=1..7 come from Omega_d = 2*pi^(d/2)/Gamma(d/2),
with Omega_7 the unique maximum in integer d. They are computed from math.gamma
at runtime; no fitted numbers.
"""

from __future__ import annotations

import argparse
import math
from pathlib import Path


def omega(d: float) -> float:
    """Surface area of the unit (d-1)-sphere: Omega_d = 2*pi^(d/2)/Gamma(d/2)."""
    return 2.0 * math.pi ** (d / 2.0) / math.gamma(d / 2.0)


def cascade_scale_stops(d_max: int = 7, extrapolation=(1.4, 1.8)) -> list[float]:
    """Scale stops: [0, Omega_1/Omega_7, ..., Omega_7/Omega_7, *extrapolation].

    A leading 0 is prepended so each ring emerges from the terminus.
    """
    peak = omega(d_max)
    ratios = [omega(d) / peak for d in range(1, d_max + 1)]
    return [0.0] + ratios + list(extrapolation)


def fmt_num(x: float, places: int = 4) -> str:
    """Format a number compactly: trim trailing zeros, drop a trailing dot."""
    s = f"{x:.{places}f}".rstrip("0").rstrip(".")
    return s if s else "0"


def build_svg(args: argparse.Namespace) -> str:
    size = args.size
    centre = size / 2.0
    r_glyph = args.glyph_radius
    stroke = args.stroke_width
    dot = args.terminus_radius

    stops = cascade_scale_stops(d_max=args.d_max, extrapolation=tuple(args.eject))
    scale_values = ";".join(fmt_num(s) for s in stops)

    # Opacity envelope over u in [0,1]:
    #   front-loaded: op at u=0, linear fall to 0 at fade_end, held at 0.
    #     (Each ring is brightest near the terminus.)
    #   peaked: 0 at u=0, rise linearly to op at t_peak, fall linearly to 0
    #     at fade_end, held at 0.  (Each ring is brightest near d_max, i.e.
    #     the cascade's Gamma-function peak; density matches an atomic
    #     radial probability cloud rather than a front-loaded core.)
    op = fmt_num(args.opacity_peak)
    fe = fmt_num(args.fade_end, places=3)
    if args.opacity_profile == "front-loaded":
        opacity_values = f"{op};0;0"
        opacity_keytimes = f"0;{fe};1"
    elif args.opacity_profile == "peaked":
        # Place the peak at the scale stop for d_max (the cascade peak).
        # Stops are equally spaced in u, so u_peak = index_of(d_max) / (n_stops-1).
        # index_of(d_max) = d_max (stops[0]=0, stops[1..d_max] = d=1..d_max).
        tp = fmt_num(args.d_max / (len(stops) - 1), places=3)
        opacity_values = f"0;{op};0;0"
        opacity_keytimes = f"0;{tp};{fe};1"
    else:
        raise ValueError(f"unknown opacity-profile: {args.opacity_profile!r}")

    layers = args.layers
    dur = args.duration
    # Phase the layers evenly through one cycle using negative begin offsets.
    offsets = [i * dur / layers for i in range(layers)]

    layer_blocks: list[str] = []
    layer_indent = "    "
    for i, offset in enumerate(offsets, start=1):
        begin_attr = "" if offset == 0 else f' begin="{fmt_num(-offset, places=3)}s"'
        block = (
            f"<!-- Layer {i} -->\n"
            f"<g>\n"
            f'  <animateTransform attributeName="transform" type="scale"\n'
            f'    values="{scale_values}"\n'
            f'    dur="{fmt_num(dur)}s"{begin_attr} repeatCount="indefinite" />\n'
            f'  <animate attributeName="opacity"\n'
            f'    values="{opacity_values}" keyTimes="{opacity_keytimes}"\n'
            f'    dur="{fmt_num(dur)}s"{begin_attr} repeatCount="indefinite" />\n'
            f'  <use href="#unit-ball" vector-effect="non-scaling-stroke" />\n'
            f"</g>"
        )
        layer_blocks.append(
            layer_indent + block.replace("\n", "\n" + layer_indent)
        )
    layers_xml = "\n\n".join(layer_blocks)

    ratios_human = ", ".join(fmt_num(s, places=2) for s in stops[1 : args.d_max + 1])

    svg = (
        f'<svg viewBox="0 0 {size} {size}" width="{size}" height="{size}" xmlns="http://www.w3.org/2000/svg"\n'
        f'     role="img" aria-label="Cascade logo: an infinite tunnel of nested unit balls descending through the cascade dimensions">\n'
        f"  <title>Cascade logo</title>\n"
        f"  <desc>\n"
        f"    Infinite tunnel of unit-ball silhouettes (circle inscribed in square)\n"
        f"    descending through the cascade dimensions. {layers} ring layers emerge\n"
        f"    phase-staggered and pass through scale stops set by the cascade\n"
        f"    ratios Omega_d / Omega_{args.d_max} for d = 1..{args.d_max}\n"
        f"    (= {ratios_human}), then eject off-canvas.\n"
        f"    With uniform time steps the ring accelerates through low d and\n"
        f"    decelerates near the Gamma-function peak at d = {args.d_max}. The\n"
        f"    central dot represents the cascade invariant terminus.\n"
        f"  </desc>\n"
        f"  <defs>\n"
        f'    <g id="unit-ball">\n'
        f'      <rect x="{fmt_num(-r_glyph)}" y="{fmt_num(-r_glyph)}"'
        f' width="{fmt_num(2*r_glyph)}" height="{fmt_num(2*r_glyph)}"\n'
        f'            fill="none" stroke="currentColor" stroke-width="{fmt_num(stroke)}" />\n'
        f'      <circle r="{fmt_num(r_glyph)}" fill="none" stroke="currentColor" stroke-width="{fmt_num(stroke)}" />\n'
        f"    </g>\n"
        f"  </defs>\n"
        f"\n"
        f'  <g transform="translate({fmt_num(centre)} {fmt_num(centre)})" color="{args.ink}" fill="none">\n'
        f"\n"
        f"    <!-- Terminus glyph: cascade invariant at the far end of the tunnel. -->\n"
        f'    <circle r="{fmt_num(dot)}" fill="currentColor" stroke="none" opacity="{fmt_num(args.terminus_opacity)}" />\n'
        f"\n"
        f"{layers_xml}\n"
        f"\n"
        f"  </g>\n"
        f"</svg>\n"
    )
    return svg


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    p = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    p.add_argument("--output", "-o", type=Path,
                   default=Path("web/assets/logo.svg"),
                   help="Output SVG path (default: web/assets/logo.svg).")
    p.add_argument("--size", type=int, default=170,
                   help="Canvas size in SVG units (default: 170).")
    p.add_argument("--glyph-radius", type=float, default=60.0,
                   help="Half-size of the unit-ball glyph before scaling (default: 60).")
    p.add_argument("--stroke-width", type=float, default=1.6,
                   help="Stroke width in SVG units (default: 1.6).")
    p.add_argument("--terminus-radius", type=float, default=1.6,
                   help="Radius of the central terminus dot (default: 1.6).")
    p.add_argument("--terminus-opacity", type=float, default=0.85,
                   help="Opacity of the terminus dot (default: 0.85).")
    p.add_argument("--ink", default="#1a1a1a",
                   help="Ink colour, set via SVG color attribute (default: #1a1a1a).")
    p.add_argument("--layers", type=int, default=12,
                   help="Number of ring layers in the tunnel (default: 12).")
    p.add_argument("--duration", type=float, default=6.0,
                   help="Animation duration in seconds per layer (default: 6).")
    p.add_argument("--d-max", type=int, default=7,
                   help="Highest cascade dimension in scale stops (default: 7; "
                        "the Gamma-function peak).")
    p.add_argument("--eject", type=float, nargs="+", default=[1.4, 1.8],
                   help="Extrapolation scale stops beyond d_max, in order "
                        "(default: 1.4 1.8).")
    p.add_argument("--opacity-peak", type=float, default=0.9,
                   help="Starting opacity of each ring (default: 0.9).")
    p.add_argument("--fade-end", type=float, default=0.70,
                   help="Normalised time (0..1) at which opacity reaches 0 "
                        "(default: 0.70).")
    p.add_argument("--opacity-profile", choices=("front-loaded", "peaked"),
                   default="front-loaded",
                   help="Shape of the per-ring opacity envelope across one "
                        "cycle. 'front-loaded' (default): ring is brightest "
                        "when smallest (near the terminus), fading as it grows. "
                        "'peaked': ring fades in from 0, peaks at the scale "
                        "stop for d_max (the cascade's Gamma-function peak), "
                        "then fades out — produces a radial-probability-cloud "
                        "density rather than a saturated core.")
    return p.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    svg = build_svg(args)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(svg, encoding="utf-8")
    print(f"wrote {args.output} ({len(svg)} bytes, {args.layers} layers, "
          f"dur={args.duration}s, fade_end={args.fade_end})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
