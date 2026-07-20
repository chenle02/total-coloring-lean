import TotalColoring

#check TotalColoring.InAuxiliaryClass
#check TotalColoring.ExtensionPalette
#check TotalColoring.HasValidRainbowColoring
#check TotalColoring.MinimalExtraction.hasValidRainbowColoring_of_inAuxiliaryClass
#check TotalColoring.Auxiliary.Extension.decode_valid
#check TotalColoring.Auxiliary.Extension.exists_valid_decode_of_inAuxiliaryClass
#check TotalColoring.Auxiliary.PairSingletonWitness
#check TotalColoring.Auxiliary.PairSingletonWitness.auxiliaryGraph
#check TotalColoring.Auxiliary.PairSingletonWitness.extension
#check TotalColoring.Auxiliary.PairSingletonWitness.classEdge_mem_distinguishedEdgeSet
#check TotalColoring.Auxiliary.PairSingletonWitness.degree_some_eq
#check TotalColoring.Auxiliary.PairSingletonWitness.card_add_degree_none_eq_two_mul_distinguished_card
#check TotalColoring.Auxiliary.PairSingletonWitness.isAuxiliaryClassMember_of_class_count_and_bounds
#check TotalColoring.Auxiliary.PairSingletonWitness.isAuxiliaryClassMember_of_highDegree
#check TotalColoring.Auxiliary.EquitableIndependentPartition
#check TotalColoring.Auxiliary.EquitableIndependentPartition.toPairSingletonWitness
#check TotalColoring.Auxiliary.EquitableIndependentPartition.distinguished_card
#check TotalColoring.Auxiliary.EquitableIndependentPartition.highDegreeWitness_inAuxiliaryClass
#check TotalColoring.Auxiliary.EquitableIndependentPartition.exists_valid_assignment_of_highDegreePartition
#check TotalColoring.MatchingLowerBound.exists_matchingGraph_edgeFinset_card_ge
#check TotalColoring.MatchingLowerBound.exists_complement_matchingGraph_edgeFinset_card_ge
#check TotalColoring.MatchingLowerBound.exists_complement_matchingGraph_edgeFinset_card_eq
#check TotalColoring.Auxiliary.exists_pairSingletonWitness_of_highDegree
#check TotalColoring.Auxiliary.exists_valid_assignment_of_highDegree_nonempty
#check TotalColoring.exists_valid_assignment_of_isEmpty
#check TotalColoring.exists_valid_assignment_of_highDegree

-- Historical proof branch `agent/independent-seed-endpoint`, source commit
-- `cc4dd7ae1d858ea0583549f88707952e2414bf60`, tree
-- `9af6a84e1305aed9a0156dcd59c279de792dea4a`.  These declarations are on
-- current `main` commit `61e79beac7d4759568187bd43a5a40f23bf83af1`,
-- tree `cb2d7d06998c213e68a7372f743f67f9cff815f7`.
#check TotalColoring.exists_valid_assignment_of_independentSeedPeel
#check TotalColoring.exists_valid_assignment_of_maxDegreeIndependentSeedPeel

-- Historical proof branch `agent/total-independent-selector-decoder`, source commit
-- `d008514c7a1cf834007bf0bd8de0d10a93926711`, tree
-- `1847934c78da03fe80bb67236868700c79016129`.  These declarations are on
-- current `main` commit `61e79beac7d4759568187bd43a5a40f23bf83af1`,
-- tree `cb2d7d06998c213e68a7372f743f67f9cff815f7`.
#check TotalColoring.SelectorCorePeelCertificate
#check TotalColoring.exists_valid_assignment_of_totalIndependentSelectorPeel
#check TotalColoring.exists_valid_assignment_of_maxDegreeTotalIndependentSelectorPeel
#check TotalColoring.AlternatingRainbowPathSelectorCertificate
#check TotalColoring.exists_valid_assignment_of_alternatingRainbowPathSelector
#check TotalColoring.exists_valid_assignment_of_maxDegreeAlternatingRainbowPathSelector

-- Historical stacked branch `agent/partial-edge-selector-normalization`, source
-- commit `c3dbe69c15f96e3c71d8481ae4e517ee2f4fdbf2`, tree
-- `11007a4aa381984a8d66aa1db297312cebe8d8b5`.  These declarations are on
-- current `main` commit `61e79beac7d4759568187bd43a5a40f23bf83af1`,
-- tree `cb2d7d06998c213e68a7372f743f67f9cff815f7`.
#check TotalColoring.EdgeAssignment.ValidOutside
#check TotalColoring.partialEdgeSelectorEdgeAssignment_valid
#check TotalColoring.partialEdgeSelectorAssignment_valid
#check TotalColoring.totalIndependentSelectorAssignment_valid_of_validOutside
#check TotalColoring.PartialEdgeSelectorNormalization
#check TotalColoring.partialEdgeSelectorNormalization_of_valid
#check TotalColoring.maxDegreePartialEdgeSelectorNormalization_of_valid

-- Proof branch `agent/donor-global-formalization`, pending merge into current
-- `main` commit `61e79beac7d4759568187bd43a5a40f23bf83af1`, tree
-- `cb2d7d06998c213e68a7372f743f67f9cff815f7`; exact endpoint
-- vertex-coloring interface only.  Physical donor-matching existence and
-- unrestricted total-coloring existence remain outside this declaration.
#check TotalColoring.adaptedSpareVertexColor_proper_iff
#check TotalColoring.Certificate.checkExtension_sound
