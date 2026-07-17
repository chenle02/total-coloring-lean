import TotalColoring.TwoColorGeometry

/-!
# Balanced exchanges preserving fixed growth witnesses

This module formalizes the exact local condition under which a simultaneous
two-color exchange preserves a color-blind ordered growth certificate.  A
certificate stores only its seed, entry edges, and old-set witnesses.  Its
entry colors are read from the current partial assignment, so the same
certificate may remain valid after those colors are exchanged.

The selected set `K` is one set of edges, not one distinguished component.
It can therefore represent a union of several physical two-color components.
Properness is handled by the existing boundary-closure interface, while
rainbow safety is handled independently by `SwapCompatibleOn`.

This is an ordinary-simple-graph statement.  It makes no hypergraph,
maximality, fan-shift, strict-descent, or coloring-existence claim.
-/

namespace TotalColoring

universe u v

namespace FixedWitness

/-- One color-blind entry of an ordered growth certificate. -/
structure Entry {V : Type u} (G : SimpleGraph V) where
  edge : G.edgeSet
  witness : V

/-- A color-blind ordered growth certificate. -/
structure Certificate {V : Type u} (G : SimpleGraph V) where
  seed : Finset V
  entries : List (Entry G)

variable {V : Type u} {G : SimpleGraph V} {C : Type v}

/-- The two endpoints of an ordinary edge, represented as a vertex finset. -/
def edgeVertices [Fintype V] [DecidableEq V] (e : G.edgeSet) : Finset V :=
  Finset.univ.filter fun vertex ↦ Incident vertex e

/-- An edge crosses a finite vertex set when it has an endpoint on each side. -/
def Crosses [DecidableEq V] (vertices : Finset V) (e : G.edgeSet) : Prop :=
  (∃ vertex, vertex ∈ vertices ∧ Incident vertex e) ∧
    ∃ vertex, vertex ∉ vertices ∧ Incident vertex e

/-- The current assignment validates an entry when the edge is colored and
its current color is missing at the stored witness. -/
def EntryValid (a : PartialEdgeAssignment G C) (entry : Entry G) : Prop :=
  ∃ color, a.color entry.edge = some color ∧
    a.MissingAt entry.witness color

/-- Recursive validity of a fixed ordered certificate from a supplied current
vertex set.  Geometry is color-blind; only `EntryValid` reads the assignment. -/
def ValidFrom [Fintype V] [DecidableEq V]
    (a : PartialEdgeAssignment G C) : Finset V → List (Entry G) → Prop
  | _vertices, [] => True
  | vertices, entry :: tail =>
      Crosses vertices entry.edge ∧
        entry.witness ∈ vertices ∧
        EntryValid a entry ∧
        ValidFrom a (vertices ∪ edgeVertices entry.edge) tail

/-- Validity of a color-blind certificate in the current assignment. -/
def Certificate.Valid [Fintype V] [DecidableEq V]
    (certificate : Certificate G) (a : PartialEdgeAssignment G C) : Prop :=
  ValidFrom a certificate.seed certificate.entries

/-- Exact local balance condition for preserving one old entry witness.

If the entry has the left swap color, its membership in `K` must agree with
that of every incident right-color edge at the witness.  The symmetric clause
handles a right-colored entry.  When the witness also misses the other color,
the corresponding universal clause is vacuous. -/
def EntrySwapCompatible (a : PartialEdgeAssignment G C) (alpha beta : C)
    (K : Set G.edgeSet) (entry : Entry G) : Prop :=
  (a.color entry.edge = some alpha →
      ∀ edge, Incident entry.witness edge →
        a.color edge = some beta →
        (entry.edge ∈ K ↔ edge ∈ K)) ∧
    (a.color entry.edge = some beta →
      ∀ edge, Incident entry.witness edge →
        a.color edge = some alpha →
        (entry.edge ∈ K ↔ edge ∈ K))

/-- Every entry of the fixed certificate satisfies the exact local balance
condition. -/
def Certificate.SwapCompatible (certificate : Certificate G)
    (a : PartialEdgeAssignment G C) (alpha beta : C)
    (K : Set G.edgeSet) : Prop :=
  ∀ entry, entry ∈ certificate.entries →
    EntrySwapCompatible a alpha beta K entry

/-- A selected set is a union of supported physical two-color components.
The reachability-saturation clause is the property used by the proofs; the
support clause records the intended literal union-of-components semantics. -/
def IsTwoColorComponentUnion (a : PartialEdgeAssignment G C)
    (alpha beta : C) (K : Set G.edgeSet) : Prop :=
  (∀ ⦃edge⦄, edge ∈ K → a.TwoColorSupported alpha beta edge) ∧
    ∀ ⦃edge other⦄, a.TwoColorReachable alpha beta edge other →
      (edge ∈ K ↔ other ∈ K)

/-- A union of whole physical two-color components cannot cut an adjacent
left-right pair. -/
theorem twoColorBoundaryClosed_of_isTwoColorComponentUnion
    (a : PartialEdgeAssignment G C) (alpha beta : C) (K : Set G.edgeSet)
    (hK : IsTwoColorComponentUnion a alpha beta K) :
    a.TwoColorBoundaryClosed alpha beta K := by
  intro edge other hadj hedge hother
  apply hK.2
  exact Relation.ReflTransGen.single
    ⟨hadj, Or.inl hedge, Or.inr hother⟩

/-- Exact one-entry criterion.  Assuming the stored witness was valid before
the exchange, it is valid for the new current entry color exactly when the
local membership equalities hold. -/
theorem entryValid_swapOn_iff [DecidableEq C]
    (a : PartialEdgeAssignment G C) (alpha beta : C)
    (K : Set G.edgeSet) [DecidablePred (· ∈ K)] (entry : Entry G)
    (hold : EntryValid a entry) :
    EntryValid (a.swapOn alpha beta K) entry ↔
      EntrySwapCompatible a alpha beta K entry := by
  rcases hold with ⟨color, hedgeColor, hwitness⟩
  constructor
  · rintro ⟨newColor, hnewEdge, hnewWitness⟩
    constructor
    · intro hedgeAlpha edge hedgeIncident hedgeBeta
      have hcolorAlpha : color = alpha :=
        Option.some.inj (hedgeColor.symm.trans hedgeAlpha)
      subst color
      by_cases hedgeK : entry.edge ∈ K
      · have hnewColorBeta : newColor = beta := by
          have h := hnewEdge
          rw [PartialEdgeAssignment.swapOn_color_of_mem
            a alpha beta K hedgeK, hedgeColor] at h
          simpa using h.symm
        constructor
        · intro _hedgeK
          by_contra hedgeNotK
          have hstillBeta :
              (a.swapOn alpha beta K).color edge = some beta := by
            simpa [PartialEdgeAssignment.swapOn_color_of_not_mem
              a alpha beta K hedgeNotK] using hedgeBeta
          exact hnewWitness edge hedgeIncident
            (by simpa [hnewColorBeta] using hstillBeta)
        · intro _hedgeK
          exact hedgeK
      · have hnewColorAlpha : newColor = alpha := by
          have h := hnewEdge
          rw [PartialEdgeAssignment.swapOn_color_of_not_mem
            a alpha beta K hedgeK, hedgeColor] at h
          exact Option.some.inj h.symm
        constructor
        · intro hedgeMem
          exact (hedgeK hedgeMem).elim
        · intro hedgeMem
          exfalso
          have hbecomesAlpha :
              (a.swapOn alpha beta K).color edge = some alpha := by
            rw [PartialEdgeAssignment.swapOn_color_of_mem
              a alpha beta K hedgeMem, hedgeBeta]
            simp
          exact hnewWitness edge hedgeIncident
            (by simpa [hnewColorAlpha] using hbecomesAlpha)
    · intro hedgeBeta edge hedgeIncident hedgeAlpha
      have hcolorBeta : color = beta :=
        Option.some.inj (hedgeColor.symm.trans hedgeBeta)
      subst color
      by_cases hedgeK : entry.edge ∈ K
      · have hnewColorAlpha : newColor = alpha := by
          have h := hnewEdge
          rw [PartialEdgeAssignment.swapOn_color_of_mem
            a alpha beta K hedgeK, hedgeColor] at h
          simpa using h.symm
        constructor
        · intro _hedgeK
          by_contra hedgeNotK
          have hstillAlpha :
              (a.swapOn alpha beta K).color edge = some alpha := by
            simpa [PartialEdgeAssignment.swapOn_color_of_not_mem
              a alpha beta K hedgeNotK] using hedgeAlpha
          exact hnewWitness edge hedgeIncident
            (by simpa [hnewColorAlpha] using hstillAlpha)
        · intro _hedgeK
          exact hedgeK
      · have hnewColorBeta : newColor = beta := by
          have h := hnewEdge
          rw [PartialEdgeAssignment.swapOn_color_of_not_mem
            a alpha beta K hedgeK, hedgeColor] at h
          exact Option.some.inj h.symm
        constructor
        · intro hedgeMem
          exact (hedgeK hedgeMem).elim
        · intro hedgeMem
          exfalso
          have hbecomesBeta :
              (a.swapOn alpha beta K).color edge = some beta := by
            rw [PartialEdgeAssignment.swapOn_color_of_mem
              a alpha beta K hedgeMem, hedgeAlpha]
            simp
          exact hnewWitness edge hedgeIncident
            (by simpa [hnewColorBeta] using hbecomesBeta)
  · intro hcompatible
    by_cases hcolorAlpha : color = alpha
    · subst color
      by_cases hedgeK : entry.edge ∈ K
      · refine ⟨beta, ?_, ?_⟩
        · rw [PartialEdgeAssignment.swapOn_color_of_mem
            a alpha beta K hedgeK, hedgeColor]
          simp
        · intro edge hedgeIncident hnew
          by_cases hedgeMem : edge ∈ K
          · rw [PartialEdgeAssignment.swapOn_color_of_mem
                a alpha beta K hedgeMem] at hnew
            cases hcolor : a.color edge with
            | none => simp [hcolor] at hnew
            | some oldColor =>
                rw [hcolor] at hnew
                simp only [Option.map_some, Option.some.injEq] at hnew
                have holdColor : oldColor = alpha := by
                  apply (Equiv.swap alpha beta).injective
                  simpa using hnew
                subst oldColor
                exact hwitness edge hedgeIncident hcolor
          · rw [PartialEdgeAssignment.swapOn_color_of_not_mem
                a alpha beta K hedgeMem] at hnew
            have hsameSide :=
              hcompatible.1 hedgeColor edge hedgeIncident hnew
            exact hedgeMem (hsameSide.mp hedgeK)
      · refine ⟨alpha, ?_, ?_⟩
        · rw [PartialEdgeAssignment.swapOn_color_of_not_mem
            a alpha beta K hedgeK, hedgeColor]
        · intro edge hedgeIncident hnew
          by_cases hedgeMem : edge ∈ K
          · rw [PartialEdgeAssignment.swapOn_color_of_mem
                a alpha beta K hedgeMem] at hnew
            cases hcolor : a.color edge with
            | none => simp [hcolor] at hnew
            | some oldColor =>
                rw [hcolor] at hnew
                simp only [Option.map_some, Option.some.injEq] at hnew
                have holdColor : oldColor = beta := by
                  apply (Equiv.swap alpha beta).injective
                  simpa using hnew
                subst oldColor
                have hsameSide :=
                  hcompatible.1 hedgeColor edge hedgeIncident hcolor
                exact hedgeK (hsameSide.mpr hedgeMem)
          · rw [PartialEdgeAssignment.swapOn_color_of_not_mem
                a alpha beta K hedgeMem] at hnew
            exact hwitness edge hedgeIncident hnew
    · by_cases hcolorBeta : color = beta
      · subst color
        by_cases hedgeK : entry.edge ∈ K
        · refine ⟨alpha, ?_, ?_⟩
          · rw [PartialEdgeAssignment.swapOn_color_of_mem
              a alpha beta K hedgeK, hedgeColor]
            simp
          · intro edge hedgeIncident hnew
            by_cases hedgeMem : edge ∈ K
            · rw [PartialEdgeAssignment.swapOn_color_of_mem
                  a alpha beta K hedgeMem] at hnew
              cases hcolor : a.color edge with
              | none => simp [hcolor] at hnew
              | some oldColor =>
                  rw [hcolor] at hnew
                  simp only [Option.map_some, Option.some.injEq] at hnew
                  have holdColor : oldColor = beta := by
                    apply (Equiv.swap alpha beta).injective
                    simpa using hnew
                  subst oldColor
                  exact hwitness edge hedgeIncident hcolor
            · rw [PartialEdgeAssignment.swapOn_color_of_not_mem
                  a alpha beta K hedgeMem] at hnew
              have hsameSide :=
                hcompatible.2 hedgeColor edge hedgeIncident hnew
              exact hedgeMem (hsameSide.mp hedgeK)
        · refine ⟨beta, ?_, ?_⟩
          · rw [PartialEdgeAssignment.swapOn_color_of_not_mem
              a alpha beta K hedgeK, hedgeColor]
          · intro edge hedgeIncident hnew
            by_cases hedgeMem : edge ∈ K
            · rw [PartialEdgeAssignment.swapOn_color_of_mem
                  a alpha beta K hedgeMem] at hnew
              cases hcolor : a.color edge with
              | none => simp [hcolor] at hnew
              | some oldColor =>
                  rw [hcolor] at hnew
                  simp only [Option.map_some, Option.some.injEq] at hnew
                  have holdColor : oldColor = alpha := by
                    apply (Equiv.swap alpha beta).injective
                    simpa using hnew
                  subst oldColor
                  have hsameSide :=
                    hcompatible.2 hedgeColor edge hedgeIncident hcolor
                  exact hedgeK (hsameSide.mpr hedgeMem)
            · rw [PartialEdgeAssignment.swapOn_color_of_not_mem
                  a alpha beta K hedgeMem] at hnew
              exact hwitness edge hedgeIncident hnew
      · refine ⟨color, ?_, ?_⟩
        · by_cases hedgeK : entry.edge ∈ K
          · rw [PartialEdgeAssignment.swapOn_color_of_mem
              a alpha beta K hedgeK, hedgeColor]
            simp [Equiv.swap_apply_of_ne_of_ne hcolorAlpha hcolorBeta]
          · rw [PartialEdgeAssignment.swapOn_color_of_not_mem
              a alpha beta K hedgeK, hedgeColor]
        · exact (PartialEdgeAssignment.missingAt_other_swapOn_iff
            a K hcolorAlpha hcolorBeta).2 hwitness

/-- Recursive form of the exact certificate criterion. -/
theorem validFrom_swapOn_iff_forall_entrySwapCompatible
    [Fintype V] [DecidableEq V]
    [DecidableEq C] (a : PartialEdgeAssignment G C) (alpha beta : C)
    (K : Set G.edgeSet) [DecidablePred (· ∈ K)]
    (seed : Finset V) (entries : List (Entry G))
    (hold : ValidFrom a seed entries) :
    ValidFrom (a.swapOn alpha beta K) seed entries ↔
    ∀ entry, entry ∈ entries →
      EntrySwapCompatible a alpha beta K entry
    := by
  induction entries generalizing seed with
  | nil => simp [ValidFrom]
  | cons entry tail ih =>
      rcases hold with ⟨hcrosses, hwitness, hentry, htail⟩
      constructor
      · rintro ⟨_crosses, _witness, hentrySwap, htailSwap⟩ current hcurrent
        rcases List.mem_cons.mp hcurrent with hcurrent | hcurrent
        · subst current
          exact (entryValid_swapOn_iff
            a alpha beta K entry hentry).1 hentrySwap
        · exact (ih (seed := seed ∪ edgeVertices entry.edge) htail).1
            htailSwap current hcurrent
      · intro hcompatible
        refine ⟨hcrosses, hwitness, ?_, ?_⟩
        · apply (entryValid_swapOn_iff
            a alpha beta K entry hentry).2
          exact hcompatible entry (by simp)
        · apply (ih (seed := seed ∪ edgeVertices entry.edge) htail).2
          intro current hcurrent
          exact hcompatible current (by simp [hcurrent])

/-- Exact certificate criterion.  Geometry and the ordered witnesses stay
literal; only the entry colors are recomputed from the swapped assignment. -/
theorem valid_swapOn_iff_swapCompatible [Fintype V] [DecidableEq V]
    [DecidableEq C] (a : PartialEdgeAssignment G C) (alpha beta : C)
    (K : Set G.edgeSet) [DecidablePred (· ∈ K)]
    (certificate : Certificate G) (hold : certificate.Valid a) :
    certificate.Valid (a.swapOn alpha beta K) ↔
      certificate.SwapCompatible a alpha beta K := by
  exact validFrom_swapOn_iff_forall_entrySwapCompatible
    a alpha beta K certificate.seed certificate.entries hold

/-- Strongest generic combined criterion supported by the existing swap API.
Boundary closure supplies properness; the two remaining conjuncts are exact. -/
theorem valid_rainbow_certificate_swapOn_iff_of_boundaryClosed
    [Fintype V] [DecidableEq V] [DecidableEq C]
    (a : PartialEdgeAssignment G C) (J K : Set G.edgeSet)
    [DecidablePred (· ∈ K)] (alpha beta : C)
    (certificate : Certificate G) (hvalid : a.Valid)
    (hrainbow : a.RainbowOn J) (halphaBeta : alpha ≠ beta)
    (hclosed : a.TwoColorBoundaryClosed alpha beta K)
    (hcertificate : certificate.Valid a) :
    (a.swapOn alpha beta K).Valid ∧
        (a.swapOn alpha beta K).RainbowOn J ∧
        certificate.Valid (a.swapOn alpha beta K) ↔
      a.SwapCompatibleOn J alpha beta K ∧
        certificate.SwapCompatible a alpha beta K := by
  have hvalidSwap : (a.swapOn alpha beta K).Valid :=
    PartialEdgeAssignment.valid_swapOn_of_boundaryClosed
      a K hvalid hclosed
  have hrainbowIff := PartialEdgeAssignment.rainbowOn_swapOn_iff
    a J K hrainbow halphaBeta
  have hcertificateIff := valid_swapOn_iff_swapCompatible
    a alpha beta K certificate hcertificate
  constructor
  · intro h
    exact ⟨hrainbowIff.mp h.2.1, hcertificateIff.mp h.2.2⟩
  · intro h
    exact ⟨hvalidSwap, hrainbowIff.mpr h.1, hcertificateIff.mpr h.2⟩

/-- Combined exact criterion for a simultaneous union of physical two-color
components. -/
theorem valid_rainbow_certificate_swapOn_iff_of_componentUnion
    [Fintype V] [DecidableEq V] [DecidableEq C]
    (a : PartialEdgeAssignment G C) (J K : Set G.edgeSet)
    [DecidablePred (· ∈ K)] (alpha beta : C)
    (certificate : Certificate G) (hvalid : a.Valid)
    (hrainbow : a.RainbowOn J) (halphaBeta : alpha ≠ beta)
    (hK : IsTwoColorComponentUnion a alpha beta K)
    (hcertificate : certificate.Valid a) :
    (a.swapOn alpha beta K).Valid ∧
        (a.swapOn alpha beta K).RainbowOn J ∧
        certificate.Valid (a.swapOn alpha beta K) ↔
      a.SwapCompatibleOn J alpha beta K ∧
        certificate.SwapCompatible a alpha beta K :=
  valid_rainbow_certificate_swapOn_iff_of_boundaryClosed
    a J K alpha beta certificate hvalid hrainbow halphaBeta
      (twoColorBoundaryClosed_of_isTwoColorComponentUnion
        a alpha beta K hK) hcertificate

/-- Two-carrier form of the simultaneous component-union criterion. -/
theorem valid_rainbow_certificate_swapOn_iff_of_componentUnion_of_uniqueCarriers
    [Fintype V] [DecidableEq V] [DecidableEq C]
    (a : PartialEdgeAssignment G C) (J K : Set G.edgeSet)
    [DecidablePred (· ∈ K)] (alpha beta : C)
    (certificate : Certificate G) {carrierAlpha carrierBeta : G.edgeSet}
    (hvalid : a.Valid) (hrainbow : a.RainbowOn J)
    (halphaBeta : alpha ≠ beta)
    (hK : IsTwoColorComponentUnion a alpha beta K)
    (hAlpha : a.IsUniqueColorOn J alpha carrierAlpha)
    (hBeta : a.IsUniqueColorOn J beta carrierBeta)
    (hcertificate : certificate.Valid a) :
    (a.swapOn alpha beta K).Valid ∧
        (a.swapOn alpha beta K).RainbowOn J ∧
        certificate.Valid (a.swapOn alpha beta K) ↔
      (carrierAlpha ∈ K ↔ carrierBeta ∈ K) ∧
        certificate.SwapCompatible a alpha beta K := by
  rw [valid_rainbow_certificate_swapOn_iff_of_componentUnion
    a J K alpha beta certificate hvalid hrainbow halphaBeta hK hcertificate,
    PartialEdgeAssignment.swapCompatibleOn_iff_of_uniqueColorOn
      a J K hAlpha hBeta]

/-- If either swap color is unused on the distinguished set, the certificate
equalities are the only remaining exact condition. -/
theorem valid_rainbow_certificate_swapOn_iff_of_componentUnion_of_oneUnused
    [Fintype V] [DecidableEq V] [DecidableEq C]
    (a : PartialEdgeAssignment G C) (J K : Set G.edgeSet)
    [DecidablePred (· ∈ K)] (alpha beta : C)
    (certificate : Certificate G) (hvalid : a.Valid)
    (hrainbow : a.RainbowOn J) (halphaBeta : alpha ≠ beta)
    (hK : IsTwoColorComponentUnion a alpha beta K)
    (hunused : a.ColorUnusedOn J alpha ∨ a.ColorUnusedOn J beta)
    (hcertificate : certificate.Valid a) :
    (a.swapOn alpha beta K).Valid ∧
        (a.swapOn alpha beta K).RainbowOn J ∧
        certificate.Valid (a.swapOn alpha beta K) ↔
      certificate.SwapCompatible a alpha beta K := by
  rw [valid_rainbow_certificate_swapOn_iff_of_componentUnion
    a J K alpha beta certificate hvalid hrainbow halphaBeta hK hcertificate]
  constructor
  · exact fun h ↦ h.2
  · intro h
    refine ⟨?_, h⟩
    rcases hunused with hunused | hunused
    · exact PartialEdgeAssignment.swapCompatibleOn_of_unused_left
        a J K hunused
    · exact PartialEdgeAssignment.swapCompatibleOn_of_unused_right
        a J K hunused

end FixedWitness

end TotalColoring
