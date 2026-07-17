import TotalColoring.CriticalCenteredRotation
import TotalColoring.CriticalDominator
import TotalColoring.CriticalGlobalMaximal
import TotalColoring.CriticalRecenteredLocation
import TotalColoring.DependencySwap

/-!
# Centered rotations at a global reachable maximum

This module packages the centered spare/carrier-label rotation as an operation
on an `OrientedOneHoleState`.  In an auxiliary critical member, a color
missing at the center is exchanged with a color unused on the distinguished
set.  The unused color is present throughout the old canonical reachable
set, while center--reachable elementarity supplies the same fact for the
center-hole color.  Consequently the centered component swap preserves every
old dependency whose source lies in that set.

At a global reach-card maximum, the resulting state has exactly the same
physical canonical reachable set and is itself globally maximal.  The old
center edge carrying the spare color becomes a non-distinguished center
target for the newly unused color, and its head lies outside the old
reachable set.  Every third color retains both its missing predicates and its
center-target data exactly.

The rotation construction uses no robust-target, dominator,
crossing-component, or `k = 2` conclusion.  The post-certificate API does
record the induced equality of third-color source columns and dominator
regions.
-/

namespace TotalColoring

universe u v

namespace PartialEdgeAssignment

variable {V : Type u} {G : SimpleGraph V} {C : Type v}

/-- A two-color swap preserves pointwise occurrence of every third color. -/
theorem swapOn_color_eq_some_iff_of_color_ne
    [DecidableEq C]
    (a : PartialEdgeAssignment G C) (K : Set G.edgeSet)
    [DecidablePred (· ∈ K)] {edge : G.edgeSet}
    {color alpha beta : C} (hcolorAlpha : color ≠ alpha)
    (hcolorBeta : color ≠ beta) :
    (a.swapOn alpha beta K).color edge = some color ↔
      a.color edge = some color := by
  by_cases hedgeK : edge ∈ K
  · constructor
    · intro hedgeColor
      rw [swapOn_color_of_mem a alpha beta K hedgeK,
        Option.map_eq_some_iff] at hedgeColor
      rcases hedgeColor with ⟨oldColor, holdColor, hswap⟩
      have holdEq : oldColor = color := by
        rw [Equiv.swap_apply_eq_iff,
          Equiv.swap_apply_of_ne_of_ne hcolorAlpha hcolorBeta] at hswap
        exact hswap
      exact holdColor.trans (congrArg some holdEq)
    · intro hedgeColor
      rw [swapOn_color_of_mem a alpha beta K hedgeK, hedgeColor]
      simp [Equiv.swap_apply_of_ne_of_ne hcolorAlpha hcolorBeta]
  · rw [swapOn_color_of_not_mem a alpha beta K hedgeK]

/-- A two-color swap preserves the center-target data of every third color.
Unlike the off-center target lemma, this statement allows the swap set to
meet the center. -/
theorem isCenterColorTarget_swapOn_iff_of_color_ne
    [DecidableEq C]
    (a : PartialEdgeAssignment G C) (J K : Set G.edgeSet)
    [DecidablePred (· ∈ K)] {center target : V}
    {color alpha beta : C} (hcolorAlpha : color ≠ alpha)
    (hcolorBeta : color ≠ beta) :
    (a.swapOn alpha beta K).IsCenterColorTarget
        J center target color ↔
      a.IsCenterColorTarget J center target color := by
  constructor
  · rintro ⟨edge, hends, hedgeJ, hedgeColor⟩
    exact ⟨edge, hends, hedgeJ,
      (swapOn_color_eq_some_iff_of_color_ne
        a K hcolorAlpha hcolorBeta).1 hedgeColor⟩
  · rintro ⟨edge, hends, hedgeJ, hedgeColor⟩
    exact ⟨edge, hends, hedgeJ,
      (swapOn_color_eq_some_iff_of_color_ne
        a K hcolorAlpha hcolorBeta).2 hedgeColor⟩

/-- When both exchanged colors are present at a source before and after a
component swap, the entire outgoing center-dependency relation at that source
is unchanged. -/
theorem centerDependency_swapOn_iff_of_source_present_both
    [DecidableEq C]
    (a : PartialEdgeAssignment G C) (J K : Set G.edgeSet)
    [DecidablePred (· ∈ K)] {center source target : V}
    {alpha beta : C}
    (holdAlpha : ¬a.MissingAt source alpha)
    (holdBeta : ¬a.MissingAt source beta)
    (hnewAlpha : ¬(a.swapOn alpha beta K).MissingAt source alpha)
    (hnewBeta : ¬(a.swapOn alpha beta K).MissingAt source beta) :
    (a.swapOn alpha beta K).CenterDependency J center source target ↔
      a.CenterDependency J center source target := by
  constructor
  · intro hdependency
    rcases hdependency with
      ⟨edge, color, hends, hedgeJ, hedgeColor, hmissing⟩
    have hcolorAlpha : color ≠ alpha := by
      intro hEq
      subst color
      exact hnewAlpha hmissing
    have hcolorBeta : color ≠ beta := by
      intro hEq
      subst color
      exact hnewBeta hmissing
    have htargetNew :
        (a.swapOn alpha beta K).IsCenterColorTarget
          J center target color :=
      ⟨edge, hends, hedgeJ, hedgeColor⟩
    have htargetOld : a.IsCenterColorTarget J center target color :=
      (isCenterColorTarget_swapOn_iff_of_color_ne
        a J K hcolorAlpha hcolorBeta).1 htargetNew
    have hmissingOld : a.MissingAt source color :=
      (missingAt_other_swapOn_iff
        a K hcolorAlpha hcolorBeta).1 hmissing
    exact (htargetOld.centerDependency_iff_missingAt source).2 hmissingOld
  · intro hdependency
    exact centerDependency_swapOn_of_source_present
      a J K hdependency holdAlpha holdBeta

end PartialEdgeAssignment

/-- The reusable output of a centered spare rotation performed at a global
canonical-reach maximum.  The certificate deliberately records the old
center in target and dependency statements; `center_eq` identifies it with
the rotated center. -/
structure CenteredSpareRotationCertificate
    {V : Type u} [Fintype V]
    {D : ℕ} {H : SimpleGraph V} {J : Finset (Sym2 V)}
    (state rotated : OrientedOneHoleState D H J)
    (alpha sigma : ExtensionPalette D) where
  alphaCarrier : H.edgeSet
  newAlphaEdge : H.edgeSet
  newAlphaTarget : V
  center_eq : rotated.center = state.center
  rootEdge_eq : rotated.root.edge = state.root.edge
  rootLeaf_eq : rotated.root.leaf = state.root.leaf
  alpha_ne_sigma : alpha ≠ sigma
  oldAlphaCarrier : state.assignment.IsUniqueColorOn
    (distinguishedEdgeSet H J) alpha alphaCarrier
  rotatedSigmaCarrier : rotated.assignment.IsUniqueColorOn
    (distinguishedEdgeSet H J) sigma alphaCarrier
  rotatedAlphaUnused : rotated.assignment.ColorUnusedOn
    (distinguishedEdgeSet H J) alpha
  newAlphaEdge_ends :
    (newAlphaEdge : Sym2 V) = s(state.center, newAlphaTarget)
  newAlphaEdge_outside : newAlphaEdge ∉ distinguishedEdgeSet H J
  oldNewAlphaEdgeColor :
    state.assignment.color newAlphaEdge = some sigma
  rotatedNewAlphaEdgeColor :
    rotated.assignment.color newAlphaEdge = some alpha
  oldSigmaTarget : state.assignment.IsCenterColorTarget
    (distinguishedEdgeSet H J) state.center newAlphaTarget sigma
  rotatedAlphaTarget : rotated.assignment.IsCenterColorTarget
    (distinguishedEdgeSet H J) rotated.center newAlphaTarget alpha
  newAlphaTarget_outside_old :
    newAlphaTarget ∉ state.canonicalReachableFinset
  oldPresent : ∀ {leaf : V},
    leaf ∈ state.canonicalReachableFinset →
      ¬state.assignment.MissingAt leaf alpha ∧
        ¬state.assignment.MissingAt leaf sigma
  rotatedPresentOnOld : ∀ {leaf : V},
    leaf ∈ state.canonicalReachableFinset →
      ¬rotated.assignment.MissingAt leaf alpha ∧
        ¬rotated.assignment.MissingAt leaf sigma
  dependency_iff_on_old : ∀ {source target : V},
    source ∈ state.canonicalReachableFinset →
      (rotated.assignment.CenterDependency
          (distinguishedEdgeSet H J) rotated.center source target ↔
        state.assignment.CenterDependency
          (distinguishedEdgeSet H J) state.center source target)
  canonicalReachableFinset_eq :
    rotated.canonicalReachableFinset = state.canonicalReachableFinset
  newAlphaTarget_outside_rotated :
    newAlphaTarget ∉ rotated.canonicalReachableFinset
  rotatedPresent : ∀ {leaf : V},
    leaf ∈ rotated.canonicalReachableFinset →
      ¬rotated.assignment.MissingAt leaf alpha ∧
        ¬rotated.assignment.MissingAt leaf sigma
  globallyMaximal : rotated.IsGloballyReachCardMaximal
  thirdMissing_iff : ∀ {gamma : ExtensionPalette D},
    gamma ≠ alpha → gamma ≠ sigma → ∀ vertex : V,
      (rotated.assignment.MissingAt vertex gamma ↔
        state.assignment.MissingAt vertex gamma)
  thirdEdgeColor_iff : ∀ {gamma : ExtensionPalette D},
    gamma ≠ alpha → gamma ≠ sigma → ∀ edge : H.edgeSet,
      (rotated.assignment.color edge = some gamma ↔
        state.assignment.color edge = some gamma)
  thirdCenterTarget_iff : ∀ {gamma : ExtensionPalette D},
    gamma ≠ alpha → gamma ≠ sigma → ∀ target : V,
      (rotated.assignment.IsCenterColorTarget
          (distinguishedEdgeSet H J) rotated.center target gamma ↔
        state.assignment.IsCenterColorTarget
          (distinguishedEdgeSet H J) state.center target gamma)

namespace CenteredSpareRotationCertificate

variable {V : Type u} [Fintype V]
variable {D : ℕ} {H : SimpleGraph V} {J : Finset (Sym2 V)}
variable {state rotated : OrientedOneHoleState D H J}
variable {alpha sigma : ExtensionPalette D}

/-- Incoming dependencies at a third-color target are unchanged globally,
not merely when their source lies in the old canonical reachable set. -/
theorem thirdColorDependency_iff
    (certificate : CenteredSpareRotationCertificate
      state rotated alpha sigma)
    {gamma : ExtensionPalette D}
    (hgammaAlpha : gamma ≠ alpha) (hgammaSigma : gamma ≠ sigma)
    {source target : V}
    (htarget : state.assignment.IsCenterColorTarget
      (distinguishedEdgeSet H J) state.center target gamma) :
    rotated.assignment.CenterDependency
        (distinguishedEdgeSet H J) rotated.center source target ↔
      state.assignment.CenterDependency
        (distinguishedEdgeSet H J) state.center source target := by
  have htargetRotated : rotated.assignment.IsCenterColorTarget
      (distinguishedEdgeSet H J) rotated.center target gamma :=
    (certificate.thirdCenterTarget_iff
      hgammaAlpha hgammaSigma target).2 htarget
  calc
    rotated.assignment.CenterDependency
          (distinguishedEdgeSet H J) rotated.center source target ↔
        rotated.assignment.MissingAt source gamma :=
      htargetRotated.centerDependency_iff_missingAt source
    _ ↔ state.assignment.MissingAt source gamma :=
      certificate.thirdMissing_iff hgammaAlpha hgammaSigma source
    _ ↔ state.assignment.CenterDependency
          (distinguishedEdgeSet H J) state.center source target :=
      (htarget.centerDependency_iff_missingAt source).symm

/-- Rooted dependency reachability is identical before and after the
centered rotation.  This is the propositional form of the recorded equality
of canonical reachable finsets. -/
theorem canonicalCenterReachable_iff
    (certificate : CenteredSpareRotationCertificate
      state rotated alpha sigma)
    (target : V) :
    rotated.assignment.CenterReachable
        (distinguishedEdgeSet H J) rotated.center rotated.root.leaf target ↔
      state.assignment.CenterReachable
        (distinguishedEdgeSet H J) state.center state.root.leaf target := by
  classical
  have hmem : target ∈ rotated.canonicalReachableFinset ↔
      target ∈ state.canonicalReachableFinset := by
    rw [certificate.canonicalReachableFinset_eq]
  simpa [OrientedOneHoleState.canonicalReachableFinset] using hmem

/-- Every rooted path avoiding a specified vertex transports through the
centered rotation.  The induction is essential: the certificate identifies
dependencies only at sources in the old canonical reachable set, and each
path prefix supplies precisely that membership. -/
theorem avoidReach_iff
    (certificate : CenteredSpareRotationCertificate
      state rotated alpha sigma)
    (q target : V) :
    DirectedDominator.AvoidReach
        (rotated.assignment.CenterDependency
          (distinguishedEdgeSet H J) rotated.center)
        rotated.root.leaf q target ↔
      DirectedDominator.AvoidReach
        (state.assignment.CenterDependency
          (distinguishedEdgeSet H J) state.center)
        state.root.leaf q target := by
  classical
  constructor
  · intro hpath
    induction hpath with
    | refl =>
        change Relation.ReflTransGen
          (DirectedDominator.Avoiding
            (state.assignment.CenterDependency
              (distinguishedEdgeSet H J) state.center) q)
          state.root.leaf rotated.root.leaf
        rw [certificate.rootLeaf_eq]
    | @tail source target hprefix hstep ih =>
        have hsourceReachRotated : rotated.assignment.CenterReachable
            (distinguishedEdgeSet H J) rotated.center
              rotated.root.leaf source := by
          exact Relation.ReflTransGen.mono
            (r := DirectedDominator.Avoiding
              (rotated.assignment.CenterDependency
                (distinguishedEdgeSet H J) rotated.center) q)
            (p := rotated.assignment.CenterDependency
              (distinguishedEdgeSet H J) rotated.center)
            (fun _ _ hedge ↦ hedge.1) rotated.root.leaf source hprefix
        have hsourceReachOld : state.assignment.CenterReachable
            (distinguishedEdgeSet H J) state.center
              state.root.leaf source :=
          (certificate.canonicalCenterReachable_iff source).1
            hsourceReachRotated
        have hsourceOld : source ∈ state.canonicalReachableFinset :=
          (PartialEdgeAssignment.mem_centerReachableFinset_iff
            state.assignment (distinguishedEdgeSet H J)
              state.center state.root.leaf source).2 hsourceReachOld
        exact Relation.ReflTransGen.tail ih
          ⟨(certificate.dependency_iff_on_old hsourceOld).1 hstep.1,
            hstep.2.1, hstep.2.2⟩
  · intro hpath
    induction hpath with
    | refl =>
        change Relation.ReflTransGen
          (DirectedDominator.Avoiding
            (rotated.assignment.CenterDependency
              (distinguishedEdgeSet H J) rotated.center) q)
          rotated.root.leaf state.root.leaf
        rw [← certificate.rootLeaf_eq]
    | @tail source target hprefix hstep ih =>
        have hsourceReachOld : state.assignment.CenterReachable
            (distinguishedEdgeSet H J) state.center
              state.root.leaf source := by
          exact Relation.ReflTransGen.mono
            (r := DirectedDominator.Avoiding
              (state.assignment.CenterDependency
                (distinguishedEdgeSet H J) state.center) q)
            (p := state.assignment.CenterDependency
              (distinguishedEdgeSet H J) state.center)
            (fun _ _ hedge ↦ hedge.1) state.root.leaf source hprefix
        have hsourceOld : source ∈ state.canonicalReachableFinset :=
          (PartialEdgeAssignment.mem_centerReachableFinset_iff
            state.assignment (distinguishedEdgeSet H J)
              state.center state.root.leaf source).2 hsourceReachOld
        exact Relation.ReflTransGen.tail ih
          ⟨(certificate.dependency_iff_on_old hsourceOld).2 hstep.1,
            hstep.2.1, hstep.2.2⟩

/-- Every vertex has the same dominator-region status before and after a
centered rotation at a global reachable maximum. -/
theorem dominatorRegion_eq
    (certificate : CenteredSpareRotationCertificate
      state rotated alpha sigma)
    (target : V) :
    rotated.dominatorRegion target = state.dominatorRegion target := by
  ext vertex
  change
    (vertex ≠ rotated.root.leaf ∧
      ¬DirectedDominator.AvoidReach
        (rotated.assignment.CenterDependency
          (distinguishedEdgeSet H J) rotated.center)
        rotated.root.leaf target vertex) ↔
    (vertex ≠ state.root.leaf ∧
      ¬DirectedDominator.AvoidReach
        (state.assignment.CenterDependency
          (distinguishedEdgeSet H J) state.center)
        state.root.leaf target vertex)
  constructor
  · rintro ⟨hroot, havoid⟩
    exact ⟨by simpa [certificate.rootLeaf_eq] using hroot,
      fun hpath ↦ havoid ((certificate.avoidReach_iff target vertex).2 hpath)⟩
  · rintro ⟨hroot, havoid⟩
    exact ⟨by simpa [certificate.rootLeaf_eq] using hroot,
      fun hpath ↦ havoid ((certificate.avoidReach_iff target vertex).1 hpath)⟩

/-- The reachable missing-source column of every third color is unchanged by
the centered rotation. -/
theorem thirdMissingSourceFinset_eq
    (certificate : CenteredSpareRotationCertificate
      state rotated alpha sigma)
    {gamma : ExtensionPalette D}
    (hgammaAlpha : gamma ≠ alpha) (hgammaSigma : gamma ≠ sigma) :
    rotated.missingSourceFinset gamma = state.missingSourceFinset gamma := by
  classical
  ext source
  simp only [OrientedOneHoleState.missingSourceFinset, Finset.mem_filter]
  rw [certificate.canonicalReachableFinset_eq,
    certificate.thirdMissing_iff hgammaAlpha hgammaSigma source]

/-- The exact external missing-source finset of every third color is
unchanged by the centered rotation. -/
theorem thirdExternalMissingSourceFinset_eq
    (certificate : CenteredSpareRotationCertificate
      state rotated alpha sigma)
    {gamma : ExtensionPalette D}
    (hgammaAlpha : gamma ≠ alpha) (hgammaSigma : gamma ≠ sigma)
    (target : V) :
    rotated.externalMissingSourceFinset target gamma =
      state.externalMissingSourceFinset target gamma := by
  classical
  ext source
  simp only [OrientedOneHoleState.mem_externalMissingSourceFinset_iff]
  rw [certificate.thirdMissingSourceFinset_eq
      hgammaAlpha hgammaSigma,
    certificate.dominatorRegion_eq target]

end CenteredSpareRotationCertificate

namespace IsOutsideEdgeMinimalNoncolorable

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {x : V}
variable {J M : Finset (Sym2 V)} [DecidableRel H.Adj]

/-- Rotate a center-hole color against a distinguished-set spare at a global
reachable maximum.  The resulting oriented one-hole state retains exactly
the old physical reachable set and all dependencies sourced there, while the
old spare center edge becomes a fresh external target for the now-unused
center-hole color. -/
theorem exists_globallyMaximal_centeredSpareRotation
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    (hstructure : IsAuxiliaryClassMember D H x J M)
    (state : OrientedOneHoleState D H J)
    (hmaximal : state.IsGloballyReachCardMaximal)
    {alpha sigma : ExtensionPalette D}
    (halphaCenter : state.assignment.MissingAt state.center alpha)
    (hsigmaUnused : state.assignment.ColorUnusedOn
      (distinguishedEdgeSet H J) sigma) :
    ∃ rotated : OrientedOneHoleState D H J,
      Nonempty (CenteredSpareRotationCertificate
        state rotated alpha sigma) := by
  classical
  let J₀ := distinguishedEdgeSet H J
  let a := state.assignment
  let center := state.center
  let root := state.root
  change a.MissingAt center alpha at halphaCenter
  change a.ColorUnusedOn J₀ sigma at hsigmaUnused
  have hrootOutside : root.edge ∉ J₀ := by
    simpa [root, J₀] using state.rootOutside
  have hvalidA : a.Valid := by
    simpa [a] using state.valid
  have honeHoleA : a.OneHoleAt root.edge := by
    simpa [a, root] using state.oneHole
  have hrainbowA : a.RainbowOn J₀ := by
    simpa [a, J₀] using state.rainbow

  have halphaSigma : alpha ≠ sigma := by
    intro hEq
    subst sigma
    exact (h.not_missingAt_center_of_unused (delta := alpha) root
      hrootOutside hvalidA honeHoleA hrainbowA hsigmaUnused)
      halphaCenter

  have hsigmaCenter : ¬a.MissingAt center sigma :=
    h.not_missingAt_center_of_unused (delta := sigma) root
      hrootOutside hvalidA honeHoleA hrainbowA hsigmaUnused
  rcases PartialEdgeAssignment.exists_incident_colored_edge_of_not_missing
      (v := center) (c := sigma) a hsigmaCenter with
    ⟨sigmaEdge, hsigmaEdgeCenter, hsigmaEdgeColor⟩
  have hsigmaEdgeOutside : sigmaEdge ∉ J₀ := by
    intro hedgeJ
    exact hsigmaUnused hedgeJ hsigmaEdgeColor
  rcases Sym2.mem_iff_exists.mp hsigmaEdgeCenter with
    ⟨vAlpha, hsigmaEdgeEnds⟩

  have halphaPresentReach : ∀ {leaf : V},
      a.CenterReachable J₀ center root.leaf leaf →
        ¬a.MissingAt leaf alpha := by
    intro leaf hreach hmissing
    exact h.center_reachable_elementary root
      hrootOutside hvalidA honeHoleA hrainbowA hreach alpha
      ⟨halphaCenter, hmissing⟩
  have hsigmaPresentReach : ∀ {leaf : V},
      a.CenterReachable J₀ center root.leaf leaf →
        ¬a.MissingAt leaf sigma := by
    intro leaf hreach
    exact h.not_missingAt_centerReachable_of_unused
      (delta := sigma) (target := leaf) hstructure root
      hrootOutside hvalidA honeHoleA hrainbowA hsigmaUnused hreach

  have hvAlphaNeRoot : vAlpha ≠ root.leaf :=
    PartialEdgeAssignment.centerTarget_ne_root_of_colored_of_oneHoleAt
      root.endpoints honeHoleA hsigmaEdgeEnds hsigmaEdgeColor
  have hvAlphaNotReach :
      ¬a.CenterReachable J₀ center root.leaf vAlpha :=
    PartialEdgeAssignment.not_centerReachable_of_center_edge_color_present_on_reachable
      hvAlphaNeRoot hsigmaEdgeEnds hsigmaEdgeColor
      (fun {source : V}
          (hsource : a.CenterReachable J₀ center root.leaf source) ↦
        hsigmaPresentReach hsource)
  have hvAlphaOutsideOld :
      vAlpha ∉ state.canonicalReachableFinset := by
    intro hmem
    have hreach : a.CenterReachable J₀ center root.leaf vAlpha := by
      simpa [OrientedOneHoleState.canonicalReachableFinset,
        a, center, root, J₀] using hmem
    exact hvAlphaNotReach hreach

  let K := a.TwoColorReachabilityClass alpha sigma sigmaEdge
  have hsigmaEdgeSupported : a.TwoColorSupported alpha sigma sigmaEdge :=
    Or.inr hsigmaEdgeColor
  have hK : a.IsTwoColorKempeComponent alpha sigma K :=
    PartialEdgeAssignment.isTwoColorKempeComponent_reachabilityClass
      a alpha sigma sigmaEdge hsigmaEdgeSupported
  have hsigmaEdgeK : sigmaEdge ∈ K :=
    PartialEdgeAssignment.root_mem_twoColorReachabilityClass
      a alpha sigma sigmaEdge
  have hKCenter : EdgeSetMeetsVertex K center :=
    ⟨sigmaEdge, hsigmaEdgeK, hsigmaEdgeCenter⟩

  let F : PartialEdgeAssignment.LinearFanPath a J₀ center :=
    { root := root
      tail := []
      root_not_mem := by simpa [root, J₀] using state.rootOutside
      chain := by simp
      nodup_spokes := by simp }
  rcases h.exists_centered_spare_rotation_of_component_meets
      (alpha := alpha) (delta := sigma) (K := K)
      F hvalidA
      (by simpa [F] using honeHoleA)
      hrainbowA halphaCenter hsigmaUnused
      hK hKCenter with
    ⟨alphaCarrier, _F', hAlphaCarrier, _hAlphaCarrierK,
      _hcompatible, hvalidSwap, hholeSwap, hrainbowSwap,
      _hsigmaCenterSwap, hAlphaUnusedSwap, hSigmaCarrierSwap,
      _hcarrierColorSwap, _hFroot, _hFtail⟩

  have hsigmaEdgeColorSwap :
      (a.swapOn alpha sigma K).color sigmaEdge = some alpha := by
    rw [PartialEdgeAssignment.swapOn_color_of_mem
      a alpha sigma K hsigmaEdgeK, hsigmaEdgeColor]
    simp

  let rotated : OrientedOneHoleState D H J :=
    { assignment := a.swapOn alpha sigma K
      center := center
      root := root
      rootOutside := hrootOutside
      valid := hvalidSwap
      oneHole := by simpa [F, root] using hholeSwap
      rainbow := by simpa [J₀] using hrainbowSwap }

  have holdPresent : ∀ {leaf : V},
      leaf ∈ state.canonicalReachableFinset →
        ¬a.MissingAt leaf alpha ∧ ¬a.MissingAt leaf sigma := by
    intro leaf hleaf
    have hreach : a.CenterReachable J₀ center root.leaf leaf := by
      simpa [OrientedOneHoleState.canonicalReachableFinset,
        a, center, root, J₀] using hleaf
    exact ⟨halphaPresentReach hreach, hsigmaPresentReach hreach⟩
  have hrotatedPresent : ∀ {leaf : V},
      leaf ∈ state.canonicalReachableFinset →
        ¬rotated.assignment.MissingAt leaf alpha ∧
          ¬rotated.assignment.MissingAt leaf sigma := by
    intro leaf hleaf
    have hpresent := holdPresent hleaf
    have hpreserved :=
      PartialEdgeAssignment.swapOn_component_preserves_present_both
        a hK halphaSigma hpresent.1 hpresent.2
    simpa [rotated] using hpreserved

  have hdependencyIff : ∀ {source target : V},
      source ∈ state.canonicalReachableFinset →
        (rotated.assignment.CenterDependency J₀ center source target ↔
          a.CenterDependency J₀ center source target) := by
    intro source target hsource
    have hold := holdPresent hsource
    have hnew := hrotatedPresent hsource
    simpa [rotated] using
      (PartialEdgeAssignment.centerDependency_swapOn_iff_of_source_present_both
        a J₀ K hold.1 hold.2
          (by simpa [rotated] using hnew.1)
          (by simpa [rotated] using hnew.2) :
        (a.swapOn alpha sigma K).CenterDependency J₀ center source target ↔
          a.CenterDependency J₀ center source target)

  have hreachableSubset : state.canonicalReachableFinset ⊆
      rotated.canonicalReachableFinset := by
    intro leaf hleaf
    have hreach : a.CenterReachable J₀ center root.leaf leaf := by
      simpa [OrientedOneHoleState.canonicalReachableFinset,
        a, center, root, J₀] using hleaf
    have hreachSwap : (a.swapOn alpha sigma K).CenterReachable
        J₀ center root.leaf leaf :=
      PartialEdgeAssignment.centerReachable_swapOn_of_reachable_sources_present
        a J₀ K
        (fun {source : V}
            (hsource : a.CenterReachable J₀ center root.leaf source) ↦
          ⟨halphaPresentReach hsource, hsigmaPresentReach hsource⟩)
        hreach
    simpa [OrientedOneHoleState.canonicalReachableFinset,
      rotated, a, center, root, J₀] using hreachSwap
  have hreachableEq : rotated.canonicalReachableFinset =
      state.canonicalReachableFinset := by
    have hcard := hmaximal rotated
    exact (Finset.eq_of_subset_of_card_le hreachableSubset (by
      simpa [OrientedOneHoleState.canonicalReachCard] using hcard)).symm
  have hrotatedMaximal : rotated.IsGloballyReachCardMaximal := by
    intro candidate
    have hle := hmaximal candidate
    simpa [OrientedOneHoleState.canonicalReachCard, hreachableEq] using hle

  refine ⟨rotated, ⟨{
    alphaCarrier := alphaCarrier
    newAlphaEdge := sigmaEdge
    newAlphaTarget := vAlpha
    center_eq := by simp [rotated, center]
    rootEdge_eq := by simp [rotated, root]
    rootLeaf_eq := by simp [rotated, root]
    alpha_ne_sigma := halphaSigma
    oldAlphaCarrier := by simpa [a, J₀] using hAlphaCarrier
    rotatedSigmaCarrier := by
      simpa [rotated, J₀] using hSigmaCarrierSwap
    rotatedAlphaUnused := by
      intro edge hedgeJ hedgeColor
      change edge ∈ J₀ at hedgeJ
      change (a.swapOn alpha sigma K).color edge = some alpha at hedgeColor
      exact hAlphaUnusedSwap hedgeJ hedgeColor
    newAlphaEdge_ends := by simpa [center] using hsigmaEdgeEnds
    newAlphaEdge_outside := by simpa [J₀] using hsigmaEdgeOutside
    oldNewAlphaEdgeColor := by simpa [a] using hsigmaEdgeColor
    rotatedNewAlphaEdgeColor := by
      simpa [rotated] using hsigmaEdgeColorSwap
    oldSigmaTarget := by
      exact ⟨sigmaEdge, by simpa [center] using hsigmaEdgeEnds,
        by simpa [J₀] using hsigmaEdgeOutside,
        by simpa [a] using hsigmaEdgeColor⟩
    rotatedAlphaTarget := by
      exact ⟨sigmaEdge, by simpa [center] using hsigmaEdgeEnds,
        by simpa [J₀] using hsigmaEdgeOutside,
        by simpa [rotated] using hsigmaEdgeColorSwap⟩
    newAlphaTarget_outside_old := hvAlphaOutsideOld
    oldPresent := by
      intro leaf hleaf
      simpa [a] using holdPresent hleaf
    rotatedPresentOnOld := hrotatedPresent
    dependency_iff_on_old := by
      intro source target hsource
      simpa [a, center, J₀] using hdependencyIff hsource
    canonicalReachableFinset_eq := hreachableEq
    newAlphaTarget_outside_rotated := by
      intro hmem
      apply hvAlphaOutsideOld
      simpa [hreachableEq] using hmem
    rotatedPresent := by
      intro leaf hleaf
      apply hrotatedPresent
      simpa [hreachableEq] using hleaf
    globallyMaximal := hrotatedMaximal
    thirdMissing_iff := by
      intro gamma hgammaAlpha hgammaSigma vertex
      simpa [rotated, a] using
        (PartialEdgeAssignment.missingAt_other_swapOn_iff
          a K hgammaAlpha hgammaSigma (v := vertex))
    thirdEdgeColor_iff := by
      intro gamma hgammaAlpha hgammaSigma edge
      simpa [rotated, a] using
        (PartialEdgeAssignment.swapOn_color_eq_some_iff_of_color_ne
          a K (edge := edge) hgammaAlpha hgammaSigma)
    thirdCenterTarget_iff := by
      intro gamma hgammaAlpha hgammaSigma target
      simpa [rotated, a, center, J₀] using
        (PartialEdgeAssignment.isCenterColorTarget_swapOn_iff_of_color_ne
          a J₀ K (center := center) (target := target)
            hgammaAlpha hgammaSigma)
  }⟩⟩

end IsOutsideEdgeMinimalNoncolorable

end TotalColoring
