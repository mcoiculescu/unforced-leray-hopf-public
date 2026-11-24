import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_1_1_8

/-!
# Part II-b, task `PartII-b:G4/4/1/1/8/3`: the first-order jet of the interaction (`BEpsJet1`)

Source of record: `the November 2 reference manuscript` (SP) lines 2007-2012, 2370-2374.
Pure calculus: `bEps p F = b_0 Q_ε F + b_1 ∂_η F + F_0 Q_ε b + F_1 ∂_η b`, `b = rawProf p`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

namespace BEpsJet1Aux

/-- The coordinate weight `1 + |s| + |η|`. -/
def jw (x : Coord) : ℝ := 1 + |x.1| + |x.2.2|

theorem one_le_jw (x : Coord) : 1 ≤ jw x := by
  unfold jw; linarith [abs_nonneg x.1, abs_nonneg x.2.2]

theorem abs_fst_le_jw (x : Coord) : |x.1| ≤ jw x := by
  unfold jw; linarith [abs_nonneg x.2.2]

theorem abs_snd_le_jw (x : Coord) : |x.2.2| ≤ jw x := by
  unfold jw; linarith [abs_nonneg x.1]

/-- The jet size: value plus first and second derivative norms at `x`. -/
def jM (G : Coord → Axi.Merid) (x : Coord) : ℝ :=
  ‖G x‖ + ‖fderiv ℝ G x‖ + ‖fderiv ℝ (fderiv ℝ G) x‖

theorem jM_nonneg (G : Coord → Axi.Merid) (x : Coord) : 0 ≤ jM G x := by
  unfold jM; positivity

theorem sum3_eq (G : Coord → Axi.Merid) (x : Coord) :
    ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l G x‖ = jM G x := by
  have h22 : ‖iteratedFDeriv ℝ 2 G x‖ = ‖fderiv ℝ (fderiv ℝ G) x‖ := by
    rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, norm_iteratedFDeriv_zero,
    norm_iteratedFDeriv_one, h22, jM]

theorem norm_flip_le (L : Coord →L[ℝ] (Coord →L[ℝ] Axi.Merid)) (e : Coord) :
    ‖L.flip e‖ ≤ ‖L‖ * ‖e‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [ContinuousLinearMap.flip_apply]
  calc ‖L v e‖ ≤ ‖L v‖ * ‖e‖ := (L v).le_opNorm e
    _ ≤ ‖L‖ * ‖v‖ * ‖e‖ := mul_le_mul_of_nonneg_right (L.le_opNorm v) (norm_nonneg _)
    _ = ‖L‖ * ‖e‖ * ‖v‖ := by ring

theorem norm_dir_le (G : Coord → Axi.Merid) (x e : Coord) (he : ‖e‖ ≤ 1) :
    ‖fderiv ℝ G x e‖ ≤ ‖fderiv ℝ G x‖ :=
  ((fderiv ℝ G x).le_opNorm e).trans (mul_le_of_le_one_right (norm_nonneg _) he)

theorem hasFDerivAt_dir {G : Coord → Axi.Merid} {x : Coord} (hG : ContDiffAt ℝ 2 G x) (e : Coord) :
    HasFDerivAt (fun y => fderiv ℝ G y e) ((fderiv ℝ (fderiv ℝ G) x).flip e) x := by
  have h1 : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) x) x :=
    ((hG.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  simpa using h1.clm_apply (hasFDerivAt_const e x)

theorem norm_smul_add_smulRight_le (c : ℝ) (D : Coord →L[ℝ] Axi.Merid) (c' : Coord →L[ℝ] ℝ)
    (m : Axi.Merid) : ‖c • D + c'.smulRight m‖ ≤ ‖c‖ * ‖D‖ + ‖c'‖ * ‖m‖ := by
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul]
  · rw [ContinuousLinearMap.norm_smulRight_apply]

theorem proj_comp_norm_le (L : Coord →L[ℝ] Axi.Merid) (i : Fin 2) :
    ‖(EuclideanSpace.proj i : Axi.Merid →L[ℝ] ℝ).comp L‖ ≤ ‖L‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  show ‖L v i‖ ≤ ‖L‖ * ‖v‖
  exact (PiLp.norm_apply_le (L v) i).trans (L.le_opNorm v)

theorem coord_hasFDerivAt {G : Coord → Axi.Merid} {x : Coord} {G' : Coord →L[ℝ] Axi.Merid}
    (hG : HasFDerivAt G G' x) (i : Fin 2) :
    HasFDerivAt (fun y => G y i) ((EuclideanSpace.proj i : Axi.Merid →L[ℝ] ℝ).comp G') x :=
  (EuclideanSpace.proj i : Axi.Merid →L[ℝ] ℝ).hasFDerivAt.comp x hG

theorem coef_fst (x : Coord) :
    ∃ D : Coord →L[ℝ] ℝ, HasFDerivAt (fun y : Coord => 2 * y.1) D x ∧ ‖D‖ ≤ 2 := by
  refine ⟨_, (hasFDerivAt_fst (p := x)).const_mul 2, ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun v => ?_
  show ‖(2:ℝ) * v.1‖ ≤ 2 * ‖v‖
  rw [norm_mul, Real.norm_two]
  exact mul_le_mul_of_nonneg_left (norm_fst_le v) (by norm_num)

theorem coef_snd (x : Coord) :
    ∃ D : Coord →L[ℝ] ℝ, HasFDerivAt (fun y : Coord => y.2.2) D x ∧ ‖D‖ ≤ 1 := by
  refine ⟨_, (hasFDerivAt_snd (p := x.2)).comp x hasFDerivAt_snd, ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  show ‖v.2.2‖ ≤ 1 * ‖v‖
  rw [one_mul]
  exact (norm_snd_le v.2).trans (norm_snd_le v)

/-- Pointwise facts about the jet of one profile. -/
theorem jet_facts (G : Coord → Axi.Merid) (x : Coord) :
    ‖G x‖ ≤ jM G x ∧ ‖fderiv ℝ G x‖ ≤ jM G x ∧ ‖fderiv ℝ (fderiv ℝ G) x‖ ≤ jM G x := by
  have hV : ‖G x‖ ≤ jM G x := by
    unfold jM; linarith [norm_nonneg (fderiv ℝ G x), norm_nonneg (fderiv ℝ (fderiv ℝ G) x)]
  have hJ : ‖fderiv ℝ G x‖ ≤ jM G x := by
    unfold jM; linarith [norm_nonneg (G x), norm_nonneg (fderiv ℝ (fderiv ℝ G) x)]
  have hH : ‖fderiv ℝ (fderiv ℝ G) x‖ ≤ jM G x := by
    unfold jM; linarith [norm_nonneg (G x), norm_nonneg (fderiv ℝ G x)]
  exact ⟨hV, hJ, hH⟩

/-- The kinetic operator `K = 2s∂_s + η∂_η` (SP 2360) has first-order jet bounded by the second
derivatives of the profile, with linear coefficients. -/
theorem kAge_jet {G : Coord → Axi.Merid} {x : Coord} (hG : ContDiffAt ℝ 2 G x) :
    ‖kAge G x‖ ≤ 2 * jw x * ‖fderiv ℝ G x‖ ∧
    ∃ L : Coord →L[ℝ] Axi.Merid, HasFDerivAt (kAge G) L x ∧
      ‖L‖ ≤ 3 * jw x * (‖fderiv ℝ G x‖ + ‖fderiv ℝ (fderiv ℝ G) x‖) := by
  have hS : ‖fderiv ℝ G x (1, ((0 : ℝ), (0 : ℝ)))‖ ≤ ‖fderiv ℝ G x‖ :=
    norm_dir_le G x _ JetLeHelp.e1_le
  have hE : ‖fderiv ℝ G x (0, ((0 : ℝ), (1 : ℝ)))‖ ≤ ‖fderiv ℝ G x‖ :=
    norm_dir_le G x _ JetLeHelp.eEta_le
  have f1 : ‖(fderiv ℝ (fderiv ℝ G) x).flip (1, ((0 : ℝ), (0 : ℝ)))‖ ≤
      ‖fderiv ℝ (fderiv ℝ G) x‖ :=
    (norm_flip_le _ _).trans (mul_le_of_le_one_right (norm_nonneg (fderiv ℝ (fderiv ℝ G) x)) JetLeHelp.e1_le)
  have f2 : ‖(fderiv ℝ (fderiv ℝ G) x).flip (0, ((0 : ℝ), (1 : ℝ)))‖ ≤
      ‖fderiv ℝ (fderiv ℝ G) x‖ :=
    (norm_flip_le _ _).trans (mul_le_of_le_one_right (norm_nonneg (fderiv ℝ (fderiv ℝ G) x)) JetLeHelp.eEta_le)
  have ha := norm_nonneg (fderiv ℝ G x)
  have ha2 := norm_nonneg (fderiv ℝ (fderiv ℝ G) x)
  have hj1 := abs_fst_le_jw x
  have hj2 := abs_snd_le_jw x
  have hw := one_le_jw x
  have k1 : ‖2 * x.1‖ = 2 * |x.1| := by rw [Real.norm_eq_abs, abs_mul, abs_two]
  have k2 : ‖x.2.2‖ = |x.2.2| := Real.norm_eq_abs _
  have hval : ‖kAge G x‖ ≤ 2 * jw x * ‖fderiv ℝ G x‖ := by
    have h1 : ‖kAge G x‖ ≤ ‖(2 * x.1) • fderiv ℝ G x (1, ((0 : ℝ), (0 : ℝ)))‖ +
        ‖x.2.2 • fderiv ℝ G x (0, ((0 : ℝ), (1 : ℝ)))‖ := norm_add_le _ _
    rw [norm_smul, norm_smul, k1, k2] at h1
    have h3 : 2 * |x.1| * ‖fderiv ℝ G x (1, ((0 : ℝ), (0 : ℝ)))‖ ≤
        2 * |x.1| * ‖fderiv ℝ G x‖ := mul_le_mul_of_nonneg_left hS (by positivity)
    have h4 : |x.2.2| * ‖fderiv ℝ G x (0, ((0 : ℝ), (1 : ℝ)))‖ ≤ |x.2.2| * ‖fderiv ℝ G x‖ :=
      mul_le_mul_of_nonneg_left hE (abs_nonneg _)
    have h5 : (2 * |x.1| + |x.2.2|) * ‖fderiv ℝ G x‖ ≤ (2 * jw x) * ‖fderiv ℝ G x‖ :=
      mul_le_mul_of_nonneg_right (by unfold jw; linarith [abs_nonneg x.1, abs_nonneg x.2.2]) ha
    nlinarith
  refine ⟨hval, ?_⟩
  obtain ⟨c1, hc1, hc1n⟩ := coef_fst x
  obtain ⟨c2, hc2, hc2n⟩ := coef_snd x
  have hdS := hasFDerivAt_dir hG (1, ((0 : ℝ), (0 : ℝ)))
  have hdE := hasFDerivAt_dir hG (0, ((0 : ℝ), (1 : ℝ)))
  refine ⟨_, (hc1.smul hdS).add (hc2.smul hdE), ?_⟩
  refine (norm_add_le _ _).trans ((add_le_add (norm_smul_add_smulRight_le _ _ _ _)
    (norm_smul_add_smulRight_le _ _ _ _)).trans ?_)
  have m1 : ‖2 * x.1‖ * ‖(fderiv ℝ (fderiv ℝ G) x).flip (1, ((0 : ℝ), (0 : ℝ)))‖ ≤
      2 * jw x * ‖fderiv ℝ (fderiv ℝ G) x‖ :=
    mul_le_mul (by rw [k1]; linarith [abs_fst_le_jw x]) f1 (norm_nonneg _) (by linarith)
  have m2 : ‖c1‖ * ‖fderiv ℝ G x (1, ((0 : ℝ), (0 : ℝ)))‖ ≤ 2 * ‖fderiv ℝ G x‖ :=
    mul_le_mul hc1n hS (norm_nonneg _) (by norm_num)
  have m3 : ‖x.2.2‖ * ‖(fderiv ℝ (fderiv ℝ G) x).flip (0, ((0 : ℝ), (1 : ℝ)))‖ ≤
      jw x * ‖fderiv ℝ (fderiv ℝ G) x‖ :=
    mul_le_mul (by rw [k2]; exact abs_snd_le_jw x) f2 (norm_nonneg _) (by linarith)
  have m4 : ‖c2‖ * ‖Axi.dEta G x‖ ≤ 1 * ‖fderiv ℝ G x‖ :=
    mul_le_mul hc2n hE (norm_nonneg _) zero_le_one
  have hA1 : ‖fderiv ℝ G x‖ ≤ jw x * ‖fderiv ℝ G x‖ := le_mul_of_one_le_left ha hw
  have hA2 : ‖fderiv ℝ (fderiv ℝ G) x‖ ≤ jw x * ‖fderiv ℝ (fderiv ℝ G) x‖ :=
    le_mul_of_one_le_left ha2 hw
  linarith

theorem smul_le_aux (c : ℝ) (v : Axi.Merid) {A B : ℝ} (hc : ‖c‖ ≤ A) (hv : ‖v‖ ≤ B) :
    ‖c • v‖ ≤ A * B := by
  rw [norm_smul]
  exact mul_le_mul hc hv (norm_nonneg _) ((norm_nonneg c).trans hc)

theorem leaf_le (c : ℝ) (D : Coord →L[ℝ] Axi.Merid) (c' : Coord →L[ℝ] ℝ) (m : Axi.Merid)
    {A B C E : ℝ} (hc : ‖c‖ ≤ A) (hD : ‖D‖ ≤ B) (hc' : ‖c'‖ ≤ C) (hm : ‖m‖ ≤ E) :
    ‖c • D + c'.smulRight m‖ ≤ A * B + C * E :=
  (norm_smul_add_smulRight_le _ _ _ _).trans
    (add_le_add (mul_le_mul hc hD (norm_nonneg _) ((norm_nonneg c).trans hc))
      (mul_le_mul hc' hm (norm_nonneg _) ((norm_nonneg c').trans hc')))

theorem qEps_jet {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {G : Coord → Axi.Merid} {x : Coord}
    (hG : ContDiffAt ℝ 2 G x) :
    ‖qEps ε G x‖ ≤ 3 * jw x * jM G x ∧
    ∃ L : Coord →L[ℝ] Axi.Merid, HasFDerivAt (qEps ε G) L x ∧ ‖L‖ ≤ 4 * jw x * jM G x := by
  obtain ⟨hk, Lk, hLk, hLkn⟩ := kAge_jet hG
  have hdQ := hasFDerivAt_dir hG (0, ((1 : ℝ), (0 : ℝ)))
  have hG' : HasFDerivAt G (fderiv ℝ G x) x := (hG.differentiableAt (by norm_num)).hasFDerivAt
  have hQ : ‖fderiv ℝ G x (0, ((1 : ℝ), (0 : ℝ)))‖ ≤ ‖fderiv ℝ G x‖ :=
    norm_dir_le G x _ JetLeHelp.eQ_le
  have f2 : ‖(fderiv ℝ (fderiv ℝ G) x).flip (0, ((1 : ℝ), (0 : ℝ)))‖ ≤
      ‖fderiv ℝ (fderiv ℝ G) x‖ :=
    (norm_flip_le _ _).trans (mul_le_of_le_one_right (norm_nonneg (fderiv ℝ (fderiv ℝ G) x))
      JetLeHelp.eQ_le)
  have hw := one_le_jw x
  obtain ⟨hV, hJ, hH⟩ := jet_facts G x
  have ha0 := norm_nonneg (G x)
  have ha1 := norm_nonneg (fderiv ℝ G x)
  have ha2 := norm_nonneg (fderiv ℝ (fderiv ℝ G) x)
  have hk0 := norm_nonneg (kAge G x)
  have hA1 : ‖fderiv ℝ G x‖ ≤ jw x * ‖fderiv ℝ G x‖ := le_mul_of_one_le_left ha1 hw
  have hA2 : ‖fderiv ℝ (fderiv ℝ G) x‖ ≤ jw x * ‖fderiv ℝ (fderiv ℝ G) x‖ :=
    le_mul_of_one_le_left ha2 hw
  have hA0 : ‖G x‖ ≤ jw x * ‖G x‖ := le_mul_of_one_le_left ha0 hw
  have hJ0 : 0 ≤ jw x * ‖G x‖ := mul_nonneg (by linarith) ha0
  have hJ1 : 0 ≤ jw x * ‖fderiv ℝ G x‖ := mul_nonneg (by linarith) ha1
  have hJ2 : 0 ≤ jw x * ‖fderiv ℝ (fderiv ℝ G) x‖ := mul_nonneg (by linarith) ha2
  refine ⟨?_, ?_⟩
  · have e1 : ‖qEps ε G x‖ ≤ ‖fderiv ℝ G x (0, ((1 : ℝ), (0 : ℝ)))‖ +
        ε * (‖kAge G x‖ + ‖G x‖) := by
      unfold qEps
      refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
      rw [norm_smul, Real.norm_of_nonneg h0]
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) h0
    have e2 : ε * (‖kAge G x‖ + ‖G x‖) ≤ ‖kAge G x‖ + ‖G x‖ :=
      mul_le_of_le_one_left (by positivity) h1
    unfold jM at hV hJ hH ⊢
    nlinarith [hk]
  · refine ⟨_, hdQ.sub ((hLk.add hG').const_smul ε), ?_⟩
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg h0]
    have f3 : ‖Lk + fderiv ℝ G x‖ ≤ ‖Lk‖ + ‖fderiv ℝ G x‖ := norm_add_le _ _
    have f4 : ε * ‖Lk + fderiv ℝ G x‖ ≤ ‖Lk‖ + ‖fderiv ℝ G x‖ :=
      (mul_le_of_le_one_left (norm_nonneg _) h1).trans f3
    unfold jM
    nlinarith [hLkn, f2, f4, hA1, hA2, hJ0, hJ1, hJ2]

theorem bEps_jet {p : UnforcedLeray.Cons.C03.Concrete.Params} (hp0 : 0 ≤ p.ε) (hp1 : p.ε ≤ 1) {F : Coord → Axi.Merid}
    {x : Coord} (hF : ContDiffAt ℝ 2 F x) (hb : ContDiffAt ℝ 2 (rawProf p) x) :
    ‖bEps p F x‖ ≤ 8 * jw x * jM (rawProf p) x * jM F x ∧
    DifferentiableAt ℝ (bEps p F) x ∧
    ‖fderiv ℝ (bEps p F) x‖ ≤ 18 * jw x * jM (rawProf p) x * jM F x := by
  obtain ⟨vF, LF, hLF, hLFn⟩ := qEps_jet hp0 hp1 hF
  obtain ⟨vb, Lb, hLb, hLbn⟩ := qEps_jet hp0 hp1 hb
  have hdF := hasFDerivAt_dir hF (0, ((0 : ℝ), (1 : ℝ)))
  have hdb := hasFDerivAt_dir hb (0, ((0 : ℝ), (1 : ℝ)))
  have hFD : HasFDerivAt F (fderiv ℝ F x) x := (hF.differentiableAt (by norm_num)).hasFDerivAt
  have hbD : HasFDerivAt (rawProf p) (fderiv ℝ (rawProf p) x) x :=
    (hb.differentiableAt (by norm_num)).hasFDerivAt
  have hH := ((coord_hasFDerivAt hbD 0).smul hLF).add ((coord_hasFDerivAt hbD 1).smul hdF)
  have hH2 := ((coord_hasFDerivAt hFD 0).smul hLb).add ((coord_hasFDerivAt hFD 1).smul hdb)
  have hbE : HasFDerivAt (bEps p F) _ x := hH.add hH2
  -- pointwise facts
  have hb0 : ‖rawProf p x 0‖ ≤ jM (rawProf p) x :=
    (PiLp.norm_apply_le _ 0).trans (jet_facts (rawProf p) x).1
  have hb1 : ‖rawProf p x 1‖ ≤ jM (rawProf p) x :=
    (PiLp.norm_apply_le _ 1).trans (jet_facts (rawProf p) x).1
  have hF0 : ‖F x 0‖ ≤ jM F x := (PiLp.norm_apply_le _ 0).trans (jet_facts F x).1
  have hF1 : ‖F x 1‖ ≤ jM F x := (PiLp.norm_apply_le _ 1).trans (jet_facts F x).1
  have hcb0 : ‖(EuclideanSpace.proj (0 : Fin 2) : Axi.Merid →L[ℝ] ℝ).comp
      (fderiv ℝ (rawProf p) x)‖ ≤ jM (rawProf p) x :=
    (proj_comp_norm_le _ 0).trans (jet_facts (rawProf p) x).2.1
  have hcb1 : ‖(EuclideanSpace.proj (1 : Fin 2) : Axi.Merid →L[ℝ] ℝ).comp
      (fderiv ℝ (rawProf p) x)‖ ≤ jM (rawProf p) x :=
    (proj_comp_norm_le _ 1).trans (jet_facts (rawProf p) x).2.1
  have hcF0 : ‖(EuclideanSpace.proj (0 : Fin 2) : Axi.Merid →L[ℝ] ℝ).comp
      (fderiv ℝ F x)‖ ≤ jM F x := (proj_comp_norm_le _ 0).trans (jet_facts F x).2.1
  have hcF1 : ‖(EuclideanSpace.proj (1 : Fin 2) : Axi.Merid →L[ℝ] ℝ).comp
      (fderiv ℝ F x)‖ ≤ jM F x := (proj_comp_norm_le _ 1).trans (jet_facts F x).2.1
  have hdFD : ‖(fderiv ℝ (fderiv ℝ F) x).flip (0, ((0 : ℝ), (1 : ℝ)))‖ ≤ jM F x :=
    (norm_flip_le _ _).trans (mul_le_of_le_one_right (norm_nonneg (fderiv ℝ (fderiv ℝ F) x))
      JetLeHelp.eEta_le |>.trans (jet_facts F x).2.2)
  have hdbD : ‖(fderiv ℝ (fderiv ℝ (rawProf p)) x).flip (0, ((0 : ℝ), (1 : ℝ)))‖ ≤
      jM (rawProf p) x :=
    (norm_flip_le _ _).trans (mul_le_of_le_one_right
      (norm_nonneg (fderiv ℝ (fderiv ℝ (rawProf p)) x)) JetLeHelp.eEta_le |>.trans
      (jet_facts (rawProf p) x).2.2)
  have hdFn : ‖fderiv ℝ F x (0, ((0 : ℝ), (1 : ℝ)))‖ ≤ jM F x :=
    (norm_dir_le F x _ JetLeHelp.eEta_le).trans (jet_facts F x).2.1
  have hdbn : ‖fderiv ℝ (rawProf p) x (0, ((0 : ℝ), (1 : ℝ)))‖ ≤ jM (rawProf p) x :=
    (norm_dir_le (rawProf p) x _ JetLeHelp.eEta_le).trans (jet_facts (rawProf p) x).2.1
  have hMM : jM (rawProf p) x * jM F x ≤ jw x * (jM (rawProf p) x * jM F x) :=
    le_mul_of_one_le_left (mul_nonneg (jM_nonneg _ _) (jM_nonneg _ _)) (one_le_jw x)
  have hval : ‖bEps p F x‖ ≤ 8 * jw x * jM (rawProf p) x * jM F x := by
    have v1 : ‖rawProf p x 0 • qEps p.ε F x‖ ≤ jM (rawProf p) x * (3 * jw x * jM F x) :=
      smul_le_aux _ _ hb0 vF
    have v2 : ‖rawProf p x 1 • Axi.dEta F x‖ ≤ jM (rawProf p) x * jM F x :=
      smul_le_aux _ _ hb1 hdFn
    have v3 : ‖F x 0 • qEps p.ε (rawProf p) x‖ ≤ jM F x * (3 * jw x * jM (rawProf p) x) :=
      smul_le_aux _ _ hF0 vb
    have v4 : ‖F x 1 • Axi.dEta (rawProf p) x‖ ≤ jM F x * jM (rawProf p) x :=
      smul_le_aux _ _ hF1 hdbn
    unfold bEps
    have t1 := norm_add_le (rawProf p x 0 • qEps p.ε F x + rawProf p x 1 • Axi.dEta F x)
      (F x 0 • qEps p.ε (rawProf p) x + F x 1 • Axi.dEta (rawProf p) x)
    have t2 := norm_add_le (rawProf p x 0 • qEps p.ε F x) (rawProf p x 1 • Axi.dEta F x)
    have t3 := norm_add_le (F x 0 • qEps p.ε (rawProf p) x) (F x 1 • Axi.dEta (rawProf p) x)
    nlinarith
  have hder : ‖fderiv ℝ (bEps p F) x‖ ≤ 18 * jw x * jM (rawProf p) x * jM F x := by
    rw [hbE.fderiv]
    have L1 := leaf_le _ _ _ _ hb0 hLFn hcb0 vF
    have L2 := leaf_le _ _ _ _ hb1 hdFD hcb1 hdFn
    have L3 := leaf_le _ _ _ _ hF0 hLbn hcF0 vb
    have L4 := leaf_le _ _ _ _ hF1 hdbD hcF1 hdbn
    refine ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add L1 L2))
      ((norm_add_le _ _).trans (add_le_add L3 L4)))).trans ?_
    nlinarith
  exact ⟨hval, hbE.differentiableAt, hder⟩

end BEpsJet1Aux

/-- **The first-order jet of the interaction** (SP 2007-2012, 2370-2374; pure calculus from
`bEps`): `‖B_εF‖ + ‖DB_εF‖ ≤ 100 (1+|s|+|η|)² (Σ_{l≤2}‖D^lF‖)(Σ_{l≤2}‖D^l b_raw‖)`. -/
theorem bEpsJet1 : UnforcedLeray.Short.IIb.BEpsJet1 := by
  refine ⟨100, by norm_num, ?_⟩
  intro p hp F hF x hb
  have hF2 : ContDiffAt ℝ 2 F x := hF.contDiffAt.of_le (by first | simp | norm_num)
  have hb2 : ContDiffAt ℝ 2 (rawProf p) x := hb.of_le (by first | simp | norm_num)
  obtain ⟨h1, h2, h3⟩ := BEpsJet1Aux.bEps_jet p.ε_pos.le hp hF2 hb2
  refine ⟨h2, ?_⟩
  rw [BEpsJet1Aux.sum3_eq F x, BEpsJet1Aux.sum3_eq (rawProf p) x]
  have hw := BEpsJet1Aux.one_le_jw x
  have hX := mul_nonneg (BEpsJet1Aux.jM_nonneg (rawProf p) x) (BEpsJet1Aux.jM_nonneg F x)
  have hsq : BEpsJet1Aux.jw x ≤ BEpsJet1Aux.jw x ^ 2 := by nlinarith
  have hjw : (1 + |x.1| + |x.2.2|) = BEpsJet1Aux.jw x := rfl
  rw [hjw]
  nlinarith [mul_le_mul_of_nonneg_right hsq hX]

end UnforcedLeray.Short.IIb

end
