import Paradox.TopologicalArtifact

/-!
# TemplateUnderdetermination: Why Covolume & Lattice Templates Admit Infinitely Many Proofs

Formalizes (`sorry`-free, pure Lean 4 core) the exact structural reason why higher-dimensional
lattice / covolume-sandwich templates can be instantiated infinitely many times:
1. `infinitely_many_geometric_witnesses`: Whenever a height/covolume sandwich
   `hMain ≤ mid(G) ≤ hMain - m * rem + budget` is satisfied via `m * rem ≤ budget` with
   `mid(G) = hMain`, **every** geometric structure `G_n` in an infinite family (`Nat → Carrier`)
   validates the sandwich—allowing infinitely many distinct "lattice proofs" of the same target.
2. `slack_dominated_sandwich_vacuous`: Whenever `m * rem ≤ budget`, the sandwich
   `∃ mid, hMain ≤ mid ∧ mid ≤ hMain - m * rem + budget` holds trivially (`mid = hMain`)
   without constraining the internal structure of `G` at all.
-/

namespace MetaCodex.Paradox

/-- Abstract covolume-sandwich predicate modeled after `h_main ≤ (V + 2δ)/d ≤ h_main - m·rem + budget`. -/
def SatisfiesCovolumeSandwich (hMain mid m rem budget : Int) : Prop :=
  hMain ≤ mid ∧ mid ≤ hMain - m * rem + budget

/-- **Anti-Template Theorem 1 (`slack_dominated_sandwich_vacuous`):**
    Whenever `m * rem ≤ budget`, there ALWAYS exists a middle term (`mid = hMain`)
    satisfying the covolume sandwich—completely independent of any geometric carrier `G`. -/
theorem slack_dominated_sandwich_vacuous (hMain m rem budget : Int)
    (hSlack : m * rem ≤ budget) :
    ∃ mid : Int, SatisfiesCovolumeSandwich hMain mid m rem budget := by
  refine ⟨hMain, Int.le_refl hMain, ?_⟩
  omega

/-- **Anti-Template Theorem 2 (`infinitely_many_geometric_witnesses`):**
    Given an infinite family of distinct geometric structures `G : Nat → Carrier`
    (e.g., `n`-dimensional lattices or theta-lift towers) whose normalized covolume term
    satisfies `mid (G n) = hMain`, if `m * rem ≤ budget` then **all infinitely many**
    geometric structures satisfy the sandwich—proving that a valid sandwich proof does not
    single out any genuine geometric mechanism. -/
theorem infinitely_many_geometric_witnesses
    {Carrier : Type u}
    (G : Nat → Carrier)
    (hDistinct : ∀ i j : Nat, i ≠ j → G i ≠ G j)
    (mid : Carrier → Int)
    (hMain m rem budget : Int)
    (hBalanced : ∀ n : Nat, mid (G n) = hMain)
    (hSlack : m * rem ≤ budget) :
    (∀ n : Nat, SatisfiesCovolumeSandwich hMain (mid (G n)) m rem budget) ∧
    (∀ i j : Nat, i ≠ j → G i ≠ G j) := by
  refine ⟨fun n => ?_, hDistinct⟩
  rw [hBalanced n]
  exact ⟨Int.le_refl hMain, by omega⟩

end MetaCodex.Paradox
