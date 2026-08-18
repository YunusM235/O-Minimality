import Aesop

declare_aesop_rule_sets [Definability]

macro "definability" : attr =>
  `(attr|aesop safe apply (rule_sets := [$(Lean.mkIdent `Definability):ident]))

/--
Aesop tactic for solving Set.Definable goals
-/
macro "definability" : tactic =>
  `(tactic| aesop (config := { terminal := true, useDefaultSimpSet := false})
    (rule_sets := [$(Lean.mkIdent `Definability):ident]))

macro "definability?" : tactic =>
  `(tactic| aesop? (config := { terminal := true, useDefaultSimpSet := false})
    (rule_sets := [$(Lean.mkIdent `Definability):ident]))
