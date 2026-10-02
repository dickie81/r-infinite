/-
No-op stand-in for LeanArchitect (https://github.com/hanwenzhu/LeanArchitect, Apache-2.0), the blueprint
tool that PrimeNumberTheoremAnd imports. It accepts the same `@[blueprint ...]` attribute and
`blueprint_comment /-- ... -/` command syntax (declarations below follow `Architect/Attribute.lean` and
`Architect/Command.lean` at v4.33.0) and records nothing, so the PNT+ files compile unchanged without the
package. Blueprint metadata has no effect on any declaration or proof.
-/
import Lean

open Lean

namespace Architect

syntax blueprintSingleUses := "-"? (ident <|> str)
syntax blueprintUses := "[" blueprintSingleUses,* "]"

syntax blueprintStatementOption := &"statement" " := " plainDocComment
syntax blueprintHasProofOption := &"hasProof" " := " (&"true" <|> &"false")
syntax blueprintProofOption := &"proof" " := " plainDocComment
syntax blueprintUsesOption := &"uses" " := " blueprintUses
syntax blueprintProofUsesOption := &"proofUses" " := " blueprintUses
syntax blueprintTitleOption := &"title" " := " (plainDocComment <|> str)
syntax blueprintNotReadyOption := &"notReady" " := " (&"true" <|> &"false")
syntax blueprintDiscussionOption := &"discussion" " := " num
syntax blueprintLatexEnvOption := &"latexEnv" " := " str
syntax blueprintLatexLabelOption := &"latexLabel" " := " str

syntax blueprintOption := "("
  blueprintStatementOption <|>
  blueprintHasProofOption <|> blueprintProofOption <|>
  blueprintUsesOption <|> blueprintProofUsesOption <|>
  blueprintTitleOption <|>
  blueprintNotReadyOption <|> blueprintDiscussionOption <|>
  blueprintLatexEnvOption <|> blueprintLatexLabelOption ")"
syntax blueprintOptions := (ppSpace str)? (ppSpace blueprintOption)*

/-- Blueprint tag (no-op here). -/
syntax (name := blueprint) "blueprint" "?"? blueprintOptions : attr

@[inherit_doc blueprint]
macro "blueprint?" opts:blueprintOptions : attr => `(attr| blueprint ? $opts)

initialize registerBuiltinAttribute {
  name := `blueprint
  descr := "blueprint node (no-op stand-in for LeanArchitect)"
  add := fun _ _ _ => pure ()
}

/-- Blueprint prose (no-op here). -/
elab (name := blueprintComment) "blueprint_comment " _stx:plainDocComment : command => pure ()

end Architect
