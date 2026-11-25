import ApspStoc

/-! Run with `lake env lean scripts/CheckAxioms.lean` after `lake build`.
Expected output for every line: `[propext, Classical.choice, Quot.sound]`. -/

-- the main theorem of the paper (Theorem 5.6 = Theorem 1.1)
#print axioms APSP.Stoc.thm_5_6
#print axioms APSP.Stoc.thm_1_1
-- the paper's own claims proved in this development
#print axioms APSP.Stoc.buildG0_of      -- Claims 3.4/3.5
#print axioms APSP.Stoc.thm_3_3         -- Theorem 3.3
#print axioms APSP.Stoc.RoutesHier.routesOK -- route length from the hierarchy of [19, 7]
#print axioms APSP.Stoc.thm_3_10        -- Theorem 3.10
#print axioms APSP.Stoc.lemma_4_2       -- Lemma 4.2
#print axioms APSP.Stoc.eo_physical     -- Lemma 5.3 (physical case)
#print axioms APSP.Stoc.lemma_5_3       -- Lemma 5.3
#print axioms APSP.Stoc.lemma_5_4       -- Lemma 5.4
#print axioms APSP.Stoc.thm_5_5         -- Theorem 5.5
-- realizability of every toolkit contract: the satisfiability model and its existence theorems
#print axioms APSP.Stoc.satToolkit
#print axioms APSP.Stoc.satToolkit_sat
#print axioms APSP.Stoc.ringSpec_realizable
#print axioms APSP.Stoc.expDecomp_exists_lg
#print axioms APSP.Stoc.route_exists
#print axioms APSP.Stoc.eoSpec_realizable
#print axioms APSP.Stoc.spanForest_exists
#print axioms APSP.Stoc.approxSpec_realizable
#print axioms APSP.Stoc.aggOf_exists
-- the CONGEST semantics: the main theorem for concrete protocols, and the [STD] contracts
#print axioms APSP.Stoc.Congest.thm_5_6_congest
#print axioms APSP.Stoc.Congest.thm_5_6_kt1
#print axioms APSP.Stoc.Congest.toToolkit
#print axioms APSP.Stoc.Congest.bindI
#print axioms APSP.Stoc.Congest.callI
#print axioms APSP.Stoc.Congest.notify_congest
#print axioms APSP.Stoc.Congest.treeCast_congest
#print axioms APSP.Stoc.Congest.clusterSetup_congest
#print axioms APSP.Stoc.expander_dist_le
-- the CONGEST semantics: the [IMPL] contracts
#print axioms APSP.Stoc.Congest.aggUp_congest          -- Lemma 2.2, upward
#print axioms APSP.Stoc.Congest.aggDown_congest        -- Lemma 2.2, downward
#print axioms APSP.Stoc.Congest.ringLE_congest         -- ring leader election
#print axioms APSP.Stoc.RingComb.ringDir_spec
#print axioms APSP.Stoc.Congest.perCompR_congest       -- per-component execution
#print axioms APSP.Stoc.Congest.rwLink_congest         -- random-walk construction of G₀
#print axioms APSP.Stoc.rwSeedMap_prob
#print axioms APSP.Stoc.Congest.embedConstruct_congest -- per-cluster preprocessing (Thm 3.10)
-- the statements of the main theorem, for inspection
#check @APSP.Stoc.Congest.thm_5_6_kt1
#check @APSP.Stoc.thm_5_6
#check @APSP.Stoc.Congest.thm_5_6_congest
