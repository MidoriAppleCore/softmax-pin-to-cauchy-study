import Mathlib
import ProofWidgets.Component.HtmlDisplay
import ProofWidgets.Component.Basic
import ProofWidgets.Data.Html
import Part4_ReplacementAxioms

/-!
# Mathgame ProofWidget

Renders the `ReplacementBlock` fields as an interactive dependency graph
directly inside the VS Code Infoview.  Place your cursor on any `#check`
or `example` below to see the widget.

The widget is pure HTML/SVG — no external JS bundle needed.  Each field of
`ReplacementBlock` becomes a node; edges show the logical flow from axioms
to the packaged block.
-/

open ProofWidgets
open scoped ProofWidgets.Jsx

namespace AnalyticTransformer

/-- Inline SVG dependency graph for the ReplacementBlock structure. -/
def replacementBlockSvg : Html :=
  .element "div" #[("style", .str "font-family: monospace; padding: 12px;")] #[
    .element "svg" #[
      ("width",   .str "520"),
      ("height",  .str "380"),
      ("viewBox", .str "0 0 520 380"),
      ("style",   .str "background:#faf5ff; border:1px solid #c4b5fd; border-radius:8px;")
    ] #[
      -- ── edges ────────────────────────────────────────────────────────
      -- ReplacementAxioms → forward_eq
      .element "line" #[("x1",.str "260"),("y1",.str "42"),
                         ("x2",.str "100"),("y2",.str "130"),
                         ("stroke",.str "#8b5cf6"),("stroke-width",.str "1.5"),
                         ("marker-end",.str "url(#arr)")] #[],
      -- ReplacementAxioms → exists_analytic
      .element "line" #[("x1",.str "260"),("y1",.str "42"),
                         ("x2",.str "260"),("y2",.str "130"),
                         ("stroke",.str "#8b5cf6"),("stroke-width",.str "1.5"),
                         ("marker-end",.str "url(#arr)")] #[],
      -- ReplacementAxioms → row_canonical
      .element "line" #[("x1",.str "260"),("y1",.str "42"),
                         ("x2",.str "420"),("y2",.str "130"),
                         ("stroke",.str "#8b5cf6"),("stroke-width",.str "1.5"),
                         ("marker-end",.str "url(#arr)")] #[],
      -- ReplacementAxioms → flow_unique
      .element "line" #[("x1",.str "260"),("y1",.str "42"),
                         ("x2",.str "130"),("y2",.str "240"),
                         ("stroke",.str "#8b5cf6"),("stroke-width",.str "1.5"),
                         ("marker-end",.str "url(#arr)")] #[],
      -- ReplacementAxioms → generator_recoverable
      .element "line" #[("x1",.str "260"),("y1",.str "42"),
                         ("x2",.str "390"),("y2",.str "240"),
                         ("stroke",.str "#8b5cf6"),("stroke-width",.str "1.5"),
                         ("marker-end",.str "url(#arr)")] #[],
      -- all fields → ReplacementBlock
      .element "line" #[("x1",.str "100"),("y1",.str "158"),
                         ("x2",.str "220"),("y2",.str "322"),
                         ("stroke",.str "#7c3aed"),("stroke-width",.str "2"),
                         ("marker-end",.str "url(#arr)")] #[],
      .element "line" #[("x1",.str "260"),("y1",.str "158"),
                         ("x2",.str "255"),("y2",.str "322"),
                         ("stroke",.str "#7c3aed"),("stroke-width",.str "2"),
                         ("marker-end",.str "url(#arr)")] #[],
      .element "line" #[("x1",.str "420"),("y1",.str "158"),
                         ("x2",.str "295"),("y2",.str "322"),
                         ("stroke",.str "#7c3aed"),("stroke-width",.str "2"),
                         ("marker-end",.str "url(#arr)")] #[],
      .element "line" #[("x1",.str "130"),("y1",.str "268"),
                         ("x2",.str "230"),("y2",.str "322"),
                         ("stroke",.str "#7c3aed"),("stroke-width",.str "2"),
                         ("marker-end",.str "url(#arr)")] #[],
      .element "line" #[("x1",.str "390"),("y1",.str "268"),
                         ("x2",.str "280"),("y2",.str "322"),
                         ("stroke",.str "#7c3aed"),("stroke-width",.str "2"),
                         ("marker-end",.str "url(#arr)")] #[],
      -- ── arrowhead marker ─────────────────────────────────────────────
      .element "defs" #[] #[
        .element "marker" #[("id",.str "arr"),("markerWidth",.str "8"),
                             ("markerHeight",.str "8"),("refX",.str "6"),
                             ("refY",.str "3"),("orient",.str "auto")] #[
          .element "path" #[("d",.str "M0,0 L0,6 L8,3 z"),
                             ("fill",.str "#7c3aed")] #[]
        ]
      ],
      -- ── nodes ────────────────────────────────────────────────────────
      -- ReplacementAxioms (root)
      .element "rect" #[("x",.str "170"),("y",.str "8"),("width",.str "180"),("height",.str "36"),
                         ("rx",.str "6"),("fill",.str "#ede9fe"),("stroke",.str "#7c3aed"),
                         ("stroke-width",.str "1.5")] #[],
      .element "text" #[("x",.str "260"),("y",.str "31"),("text-anchor",.str "middle"),
                         ("font-size",.str "11"),("fill",.str "#4c1d95"),
                         ("font-weight",.str "bold")] #[.text "ReplacementAxioms θ"],
      -- forward_eq
      .element "rect" #[("x",.str "28"),("y",.str "120"),("width",.str "144"),("height",.str "38"),
                         ("rx",.str "5"),("fill",.str "#f5f3ff"),("stroke",.str "#a78bfa")] #[],
      .element "text" #[("x",.str "100"),("y",.str "137"),("text-anchor",.str "middle"),
                         ("font-size",.str "10"),("fill",.str "#5b21b6")] #[.text "forward_eq"],
      .element "text" #[("x",.str "100"),("y",.str "151"),("text-anchor",.str "middle"),
                         ("font-size",.str "9"),("fill",.str "#7c3aed")] #[.text "analyticFwd = gpt2Fwd"],
      -- exists_analytic
      .element "rect" #[("x",.str "178"),("y",.str "120"),("width",.str "164"),("height",.str "38"),
                         ("rx",.str "5"),("fill",.str "#f5f3ff"),("stroke",.str "#a78bfa")] #[],
      .element "text" #[("x",.str "260"),("y",.str "137"),("text-anchor",.str "middle"),
                         ("font-size",.str "10"),("fill",.str "#5b21b6")] #[.text "exists_analytic"],
      .element "text" #[("x",.str "260"),("y",.str "151"),("text-anchor",.str "middle"),
                         ("font-size",.str "9"),("fill",.str "#7c3aed")] #[.text "∃ φ, analyticFwd φ = gpt2Fwd θ"],
      -- row_canonical
      .element "rect" #[("x",.str "348"),("y",.str "120"),("width",.str "144"),("height",.str "38"),
                         ("rx",.str "5"),("fill",.str "#f5f3ff"),("stroke",.str "#a78bfa")] #[],
      .element "text" #[("x",.str "420"),("y",.str "137"),("text-anchor",.str "middle"),
                         ("font-size",.str "10"),("fill",.str "#5b21b6")] #[.text "row_canonical"],
      .element "text" #[("x",.str "420"),("y",.str "151"),("text-anchor",.str "middle"),
                         ("font-size",.str "9"),("fill",.str "#7c3aed")] #[.text "p = scorePoles scores q"],
      -- flow_unique
      .element "rect" #[("x",.str "50"),("y",.str "228"),("width",.str "160"),("height",.str "40"),
                         ("rx",.str "5"),("fill",.str "#f5f3ff"),("stroke",.str "#a78bfa")] #[],
      .element "text" #[("x",.str "130"),("y",.str "246"),("text-anchor",.str "middle"),
                         ("font-size",.str "10"),("fill",.str "#5b21b6")] #[.text "flow_unique"],
      .element "text" #[("x",.str "130"),("y",.str "260"),("text-anchor",.str "middle"),
                         ("font-size",.str "9"),("fill",.str "#7c3aed")] #[.text "Φ = cauchyResidualFlow"],
      -- generator_recoverable
      .element "rect" #[("x",.str "305"),("y",.str "228"),("width",.str "170"),("height",.str "40"),
                         ("rx",.str "5"),("fill",.str "#f5f3ff"),("stroke",.str "#a78bfa")] #[],
      .element "text" #[("x",.str "390"),("y",.str "246"),("text-anchor",.str "middle"),
                         ("font-size",.str "10"),("fill",.str "#5b21b6")] #[.text "generator_recoverable"],
      .element "text" #[("x",.str "390"),("y",.str "260"),("text-anchor",.str "middle"),
                         ("font-size",.str "9"),("fill",.str "#7c3aed")] #[.text "cauchyLinearOp = deriv Φ 0"],
      -- ReplacementBlock (sink)
      .element "rect" #[("x",.str "170"),("y",.str "322"),("width",.str "180"),("height",.str "40"),
                         ("rx",.str "6"),("fill",.str "#7c3aed"),("stroke",.str "#4c1d95"),
                         ("stroke-width",.str "2")] #[],
      .element "text" #[("x",.str "260"),("y",.str "339"),("text-anchor",.str "middle"),
                         ("font-size",.str "11"),("fill",.str "white"),
                         ("font-weight",.str "bold")] #[.text "ReplacementBlock θ"],
      .element "text" #[("x",.str "260"),("y",.str "354"),("text-anchor",.str "middle"),
                         ("font-size",.str "9"),("fill",.str "#ddd6fe")] #[.text "ReplacementAxioms θ ⟹ ReplacementBlock θ"]
    ]
  ]

/-- Widget component: renders `replacementBlockSvg` in the Infoview. -/
@[widget_module]
def ReplacementBlockWidget : Component Unit where
  javascript := "
    import * as React from 'react';
    export default function(props) {
      return React.createElement('div', {
        dangerouslySetInnerHTML: { __html: props.html }
      });
    }
  "

-- ── Usage: place your cursor on the #check below ──────────────────────────

/-- Show the ReplacementBlock dependency graph in the Infoview. -/
#html replacementBlockSvg

end AnalyticTransformer
