import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Static.Fried

/-!
# `PartIII-a:T21/2/7/2/1/1/5/18/2`: the commutator `[∂^w, v·∇]` (`StTransComm`)

Source of record: `the November 2 reference manuscript` lines 3060-3071
("differentiated weighted energy": the derivatives of the transport term are of the order of the
energy).  The derivation rule `∂_j(a·∇H) = (∂_ja)·∇H + a·∇(∂_jH)` (`st_pdCx_stGrad`, product rule and
`StAdjComm`) and `st_word_leibniz` give `∂^w(v·∇G) = Σ_{p ∈ stSplits w} (∂^{p.1}v)·∇(∂^{p.2}G)`; the
head splitting `([], w)` is `v·∇∂^wG` and every other term has `|p.1| ≥ 1`, hence involves only the
derivatives `∂_l∂^{p.2}G = ∂^{l :: p.2}G` of order `≤ |w|`, with coefficients bounded by
`StVelWords`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem st_pdCx_ofReal_mul {b : ℝ × ℝ → ℝ} {H : ℝ × ℝ → ℂ} (hb : Differentiable ℝ b)
    (hH : Differentiable ℝ H) (j : Fin 2) :
    pdCx j (fun x => ((b x : ℝ) : ℂ) * H x) =
      fun x => ((B0579.pd j b x : ℝ) : ℂ) * H x + ((b x : ℝ) : ℂ) * pdCx j H x := by
  funext x
  have hb' : HasFDerivAt (fun y => ((b y : ℝ) : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ b x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x (hb x).hasFDerivAt
  have hprod : HasFDerivAt (fun y => ((b y : ℝ) : ℂ) * H y)
      (((b x : ℝ) : ℂ) • fderiv ℝ H x + H x • Complex.ofRealCLM.comp (fderiv ℝ b x)) x :=
    hb'.mul (hH x).hasFDerivAt
  unfold pdCx
  rw [hprod.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul, B0579.pd]
  ring

theorem st_contDiff_stGrad' {a : Fin 2 → ℝ × ℝ → ℝ} (ha : ∀ l, ContDiff ℝ ∞ (a l))
    {H : ℝ × ℝ → ℂ} (hH : ContDiff ℝ ∞ H) : ContDiff ℝ ∞ (stGrad a H) := by
  have h : ∀ l : Fin 2, ContDiff ℝ ∞ (fun x => ((a l x : ℝ) : ℂ) * pdCx l H x) :=
    fun l => (Complex.ofRealCLM.contDiff.comp (ha l)).mul (st_contDiff_pdCx hH l)
  unfold stGrad
  simp only [Fin.sum_univ_two]
  exact (h 0).add (h 1)

/-- The derivation rule `∂_j(a·∇H) = (∂_ja)·∇H + a·∇(∂_jH)`. -/
theorem st_pdCx_stGrad (hComm : StAdjComm) {a : Fin 2 → ℝ × ℝ → ℝ}
    (ha : ∀ l, ContDiff ℝ ∞ (a l)) {H : ℝ × ℝ → ℂ} (hH : ContDiff ℝ ∞ H) (j : Fin 2) :
    pdCx j (stGrad a H) = fun x =>
      stGrad (fun l => B0579.pd j (a l)) H x + stGrad a (pdCx j H) x := by
  have hterm : ∀ l : Fin 2, pdCx j (fun x => ((a l x : ℝ) : ℂ) * pdCx l H x) = fun x =>
      ((B0579.pd j (a l) x : ℝ) : ℂ) * pdCx l H x + ((a l x : ℝ) : ℂ) * pdCx l (pdCx j H) x := by
    intro l
    rw [st_pdCx_ofReal_mul ((ha l).differentiable (by simp))
      (st_differentiable (st_contDiff_pdCx hH l)) j]
    have hsym : pdCx j (pdCx l H) = pdCx l (pdCx j H) := hComm H hH [j] l
    rw [hsym]
  have hd : ∀ l : Fin 2, Differentiable ℝ (fun x => ((a l x : ℝ) : ℂ) * pdCx l H x) :=
    fun l => st_differentiable
      ((Complex.ofRealCLM.contDiff.comp (ha l)).mul (st_contDiff_pdCx hH l))
  unfold stGrad
  simp only [Fin.sum_univ_two]
  rw [st_pdCx_add (hd 0) (hd 1), hterm 0, hterm 1]
  funext x
  ring

/-- `‖b·∇H‖ ≤ A Σ_l ‖∂_lH‖` for `|b_l| ≤ A`. -/
theorem st_stGrad_bound {c m : ℝ} {b : Fin 2 → ℝ × ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hbc : ∀ l, Continuous (b l)) (hb : ∀ l (x : ℝ × ℝ), |b l x| ≤ A) {H : ℝ × ℝ → ℂ}
    (hH : ∀ l : Fin 2, MemLp (pdCx l H) 2 (B0579.cellMeasure c (-m))) :
    MemLp (stGrad b H) 2 (B0579.cellMeasure c (-m)) ∧
      (xNorm c (-m) (stGrad b H)).toReal ≤
        A * ∑ l : Fin 2, (xNorm c (-m) (pdCx l H)).toReal := by
  have hterm : ∀ l : Fin 2, MemLp (fun x => ((b l x : ℝ) : ℂ) * pdCx l H x) 2
      (B0579.cellMeasure c (-m)) ∧
      (xNorm c (-m) (fun x => ((b l x : ℝ) : ℂ) * pdCx l H x)).toReal ≤
        A * (xNorm c (-m) (pdCx l H)).toReal := by
    intro l
    have hle : ∀ᵐ x ∂(B0579.cellMeasure c (-m)),
        ‖((b l x : ℝ) : ℂ) * pdCx l H x‖ ≤ A * ‖pdCx l H x‖ := by
      refine ae_of_all _ fun x => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hb l x) (norm_nonneg _)
    have hmeas : AEStronglyMeasurable (fun x => ((b l x : ℝ) : ℂ) * pdCx l H x)
        (B0579.cellMeasure c (-m)) :=
      (Complex.continuous_ofReal.comp (hbc l)).aestronglyMeasurable.mul (hH l).1
    refine ⟨(hH l).of_le_mul hmeas hle, ?_⟩
    have h := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hle 2
    have hfin := (hH l).eLpNorm_lt_top.ne
    calc (xNorm c (-m) (fun x => ((b l x : ℝ) : ℂ) * pdCx l H x)).toReal
        ≤ (ENNReal.ofReal A * xNorm c (-m) (pdCx l H)).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) h
      _ = A * (xNorm c (-m) (pdCx l H)).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA]
  obtain ⟨hm0, hb0⟩ := hterm 0
  obtain ⟨hm1, hb1⟩ := hterm 1
  have e : stGrad b H = (fun x => ((b 0 x : ℝ) : ℂ) * pdCx 0 H x) +
      fun x => ((b 1 x : ℝ) : ℂ) * pdCx 1 H x := by
    funext x
    simp [stGrad, Fin.sum_univ_two]
  rw [e, Fin.sum_univ_two]
  refine ⟨hm0.add hm1, ?_⟩
  have h := eLpNorm_add_le hm0.1 hm1.1 (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hne0 := hm0.eLpNorm_lt_top.ne
  have hne1 := hm1.eLpNorm_lt_top.ne
  calc (xNorm c (-m) ((fun x => ((b 0 x : ℝ) : ℂ) * pdCx 0 H x) +
        fun x => ((b 1 x : ℝ) : ℂ) * pdCx 1 H x)).toReal
      ≤ (xNorm c (-m) (fun x => ((b 0 x : ℝ) : ℂ) * pdCx 0 H x) +
          xNorm c (-m) (fun x => ((b 1 x : ℝ) : ℂ) * pdCx 1 H x)).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hne0, hne1⟩) h
    _ = (xNorm c (-m) (fun x => ((b 0 x : ℝ) : ℂ) * pdCx 0 H x)).toReal +
          (xNorm c (-m) (fun x => ((b 1 x : ℝ) : ℂ) * pdCx 1 H x)).toReal :=
        ENNReal.toReal_add hne0 hne1
    _ ≤ A * (xNorm c (-m) (pdCx 0 H)).toReal + A * (xNorm c (-m) (pdCx 1 H)).toReal :=
        add_le_add hb0 hb1
    _ = A * ((xNorm c (-m) (pdCx 0 H)).toReal + (xNorm c (-m) (pdCx 1 H)).toReal) := by ring

/-- **`StTransComm` from its leaves.** -/
theorem stTransComm_of (hComm : StAdjComm) (hVW : StVelWords) : StTransComm := by
  intro c m k Av
  have hA0 : 0 ≤ ∑ i ∈ Finset.range (k + 1), |Av i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨2 ^ k * (2 * ∑ i ∈ Finset.range (k + 1), |Av i|), by positivity, ?_⟩
  intro v hv G hGs hGm w hw
  have hcs : ∀ (u : List (Fin 2)) (l : Fin 2), ContDiff ℝ ∞ (stCoefWord u (stVel v) l) :=
    fun u l => (hVW c v Av hv u l).1
  have hexp : adjSpatial w (stGrad (stVel v) G) = fun x =>
      ((stSplits w).map fun p => stGrad (stCoefWord p.1 (stVel v)) (adjSpatial p.2 G) x).sum :=
    st_word_leibniz stGrad (stVel v) (fun u => adjSpatial u G) w.length
      (fun u u' _ => st_contDiff_stGrad' (hcs u) (st_contDiff_adjSpatial hGs u'))
      (fun j u u' _ => st_pdCx_stGrad hComm (hcs u) (st_contDiff_adjSpatial hGs u') j) w le_rfl
  obtain ⟨T, hT, hT1⟩ := st_splits_cons_head w
  have hc0 : stCoefWord [] (stVel v) = stVel v := rfl
  have hcomm : (fun x => adjSpatial w (stGrad (stVel v) G) x -
      stGrad (stVel v) (adjSpatial w G) x) = fun x =>
      (T.map fun p => stGrad (stCoefWord p.1 (stVel v)) (adjSpatial p.2 G) x).sum := by
    funext x
    rw [hexp]
    simp only [hT, List.map_cons, List.sum_cons, hc0]
    ring
  rw [hcomm]
  -- the bound of each term
  have hterm : ∀ p ∈ T, MemLp (stGrad (stCoefWord p.1 (stVel v)) (adjSpatial p.2 G)) 2
      (B0579.cellMeasure c (-m)) ∧
      (xNorm c (-m) (stGrad (stCoefWord p.1 (stVel v)) (adjSpatial p.2 G))).toReal ≤
        (∑ i ∈ Finset.range (k + 1), |Av i|) *
          (2 * ∑ u ∈ wordsLE w.length, (xNorm c (-m) (adjSpatial u G)).toReal) := by
    intro p hp
    have hpS : p ∈ stSplits w := by rw [hT]; exact List.mem_cons_of_mem _ hp
    have hlen := st_splits_length p hpS
    have hp1 := hT1 p hp
    have hAp : ∀ (l : Fin 2) (x : ℝ × ℝ),
        |stCoefWord p.1 (stVel v) l x| ≤ ∑ i ∈ Finset.range (k + 1), |Av i| := by
      intro l x
      exact ((hVW c v Av hv p.1 l).2.2.1 x).trans ((le_abs_self _).trans
        (Finset.single_le_sum (f := fun i => |Av i|) (fun _ _ => abs_nonneg _)
          (Finset.mem_range.2 (by omega))))
    obtain ⟨hm, hb⟩ := st_stGrad_bound hA0 (fun l => (hcs p.1 l).continuous) hAp
      (H := adjSpatial p.2 G) fun l => hGm (l :: p.2)
    refine ⟨hm, hb.trans (mul_le_mul_of_nonneg_left ?_ hA0)⟩
    have hle : ∀ l : Fin 2, (xNorm c (-m) (adjSpatial (l :: p.2) G)).toReal ≤
        ∑ u ∈ wordsLE w.length, (xNorm c (-m) (adjSpatial u G)).toReal := by
      intro l
      have hmem : (l :: p.2) ∈ wordsLE w.length := mem_wordsLE.2 (by simp; omega)
      exact Finset.single_le_sum (f := fun u => (xNorm c (-m) (adjSpatial u G)).toReal)
        (fun _ _ => ENNReal.toReal_nonneg) hmem
    have h0 := hle 0
    have h1 := hle 1
    rw [Fin.sum_univ_two]
    show (xNorm c (-m) (adjSpatial (0 :: p.2) G)).toReal +
        (xNorm c (-m) (adjSpatial (1 :: p.2) G)).toReal ≤ _
    linarith
  obtain ⟨hm, hb⟩ := st_list_sum_memLp_le T
    (fun p => stGrad (stCoefWord p.1 (stVel v)) (adjSpatial p.2 G))
    (fun _ => (∑ i ∈ Finset.range (k + 1), |Av i|) *
      (2 * ∑ u ∈ wordsLE w.length, (xNorm c (-m) (adjSpatial u G)).toReal)) hterm
  refine ⟨hm, hb.trans ?_⟩
  rw [List.map_const', List.sum_replicate, nsmul_eq_mul]
  have hTlen : T.length + 1 = 2 ^ w.length := by
    have := st_splits_card w
    rw [hT, List.length_cons] at this
    exact this
  have hTk : (T.length : ℝ) ≤ 2 ^ k := by
    have h1 : T.length ≤ 2 ^ w.length := by omega
    have h2 : 2 ^ w.length ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hw
    exact_mod_cast h1.trans h2
  have hSe0 : 0 ≤ ∑ u ∈ wordsLE w.length, (xNorm c (-m) (adjSpatial u G)).toReal :=
    Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hpos : 0 ≤ (∑ i ∈ Finset.range (k + 1), |Av i|) *
      (2 * ∑ u ∈ wordsLE w.length, (xNorm c (-m) (adjSpatial u G)).toReal) :=
    mul_nonneg hA0 (mul_nonneg zero_le_two hSe0)
  calc (T.length : ℝ) * ((∑ i ∈ Finset.range (k + 1), |Av i|) *
        (2 * ∑ u ∈ wordsLE w.length, (xNorm c (-m) (adjSpatial u G)).toReal))
      ≤ 2 ^ k * ((∑ i ∈ Finset.range (k + 1), |Av i|) *
        (2 * ∑ u ∈ wordsLE w.length, (xNorm c (-m) (adjSpatial u G)).toReal)) :=
        mul_le_mul_of_nonneg_right hTk hpos
    _ = 2 ^ k * (2 * ∑ i ∈ Finset.range (k + 1), |Av i|) *
        ∑ u ∈ wordsLE w.length, (xNorm c (-m) (adjSpatial u G)).toReal := by ring

end UnforcedLeray.Short.IIIa
