import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L2

/-!
# `SepGapPointwise` (`PartIII-b:IIIb-D2/3/1/1/2/4`)

Source 3604-3621 (`sep:kernel`).  Off the support of `T` the integrand vanishes; on it,
`|y - l z| ≥ c (1 + l|z|)` for `y` near `y₀` in the gap, and `sep:kernel` bounds the derivatives.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

lemma L4_term (K : Space → ℝ) (hK : ContDiff ℝ 3 K) (c : ℂ) (e w y : Space) (n : ℕ) (hn : n ≤ 2) :
    ‖iteratedFDeriv ℝ n (fun y' => c * (((fderiv ℝ K (y' - w) e : ℝ)) : ℂ)) y‖ ≤
      ‖c‖ * ‖e‖ * ‖iteratedFDeriv ℝ (n + 1) K (y - w)‖ := by
  have h1 : ContDiff ℝ 2 (fun y' : Space => fderiv ℝ K (y' - w)) :=
    ((hK.fderiv_right (by norm_num)).comp (contDiff_id.sub contDiff_const))
  let L : (Space →L[ℝ] ℝ) →L[ℝ] ℂ :=
    (c • Complex.ofRealCLM).comp (ContinuousLinearMap.apply ℝ ℝ e)
  have hL : ∀ f : Space →L[ℝ] ℝ, L f = c * ((f e : ℝ) : ℂ) := by
    intro f; simp [L]
  have hfun : (fun y' : Space => c * (((fderiv ℝ K (y' - w) e : ℝ)) : ℂ)) =
      L ∘ (fun y' : Space => fderiv ℝ K (y' - w)) := by
    funext y'; simp [hL]
  have hLn : ‖L‖ ≤ ‖c‖ * ‖e‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun f => ?_
    rw [hL, norm_mul, Complex.norm_real]
    have : ‖f e‖ ≤ ‖f‖ * ‖e‖ := f.le_opNorm e
    nlinarith [norm_nonneg c, norm_nonneg f, norm_nonneg e]
  rw [hfun]
  have h2 := L.norm_iteratedFDeriv_comp_left (f := fun y' : Space => fderiv ℝ K (y' - w))
    (x := y) (N := 2) (n := n) (h1.contDiffAt) (by exact_mod_cast hn)
  refine h2.trans ?_
  have h3 : iteratedFDeriv ℝ n (fun y' : Space => fderiv ℝ K (y' - w)) y =
      iteratedFDeriv ℝ n (fderiv ℝ K) (y - w) := iteratedFDeriv_comp_sub (f := fderiv ℝ K) n w y
  rw [h3, norm_iteratedFDeriv_fderiv]
  exact mul_le_mul_of_nonneg_right hLn (norm_nonneg _)

lemma L4_sum {ι : Type} (u : Finset ι) (f : ι → Space → ℂ) (n : ℕ)
    (hf : ∀ i ∈ u, ContDiff ℝ 2 (f i)) (hn : n ≤ 2) (y : Space) :
    ‖iteratedFDeriv ℝ n (fun w => ∑ i ∈ u, f i w) y‖ ≤ ∑ i ∈ u, ‖iteratedFDeriv ℝ n (f i) y‖ := by
  rw [iteratedFDeriv_fun_sum_apply (fun i hi => ((hf i hi).of_le (by exact_mod_cast hn)).contDiffAt)]
  exact norm_sum_le _ _

lemma L4_term_cd (K : Space → ℝ) (hK : ContDiff ℝ 3 K) (c : ℂ) (e w : Space) :
    ContDiff ℝ 2 (fun y' : Space => c * (((fderiv ℝ K (y' - w) e : ℝ)) : ℂ)) := by
  have h1 : ContDiff ℝ 2 (fun y' : Space => fderiv ℝ K (y' - w)) :=
    ((hK.fderiv_right (by norm_num)).comp (contDiff_id.sub contDiff_const))
  exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (h1.clm_apply contDiff_const))

lemma L4_phi (ν : ℝ) (μ : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (i : Fin 3)
    (l : ℝ) (z : Space) (hl : l ∈ Ioo (0 : ℝ) 1) (hν : 0 < ν) (h2 : HeatLerayKSmooth)
    (n : ℕ) (hn : n ≤ 2) (y : Space) :
    ‖iteratedFDeriv ℝ n (sepPhi ν μ T τ i (l, z)) y‖ ≤
      ∑ j : Fin 3, ∑ k : Fin 3, ‖(-2 * (l : ℂ) ^ (2 * μ + 2) *
          ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ))‖ * ‖coordinateVector k‖ *
        ‖iteratedFDeriv ℝ (n + 1) (fun x => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x)
          (y - l • z)‖ := by
  have ht : 0 < ν * (1 - l ^ 2) := by
    have := hl.1; have := hl.2; nlinarith [mul_pos hν (sub_pos.2 (show l ^ 2 < 1 by nlinarith))]
  have hK : ∀ j, ContDiff ℝ 3 (fun x => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x) :=
    fun j => h2 _ ht i j
  have hfun : sepPhi ν μ T τ i (l, z) = fun y' => ∑ j : Fin 3, ∑ k : Fin 3,
      (-2 * (l : ℂ) ^ (2 * μ + 2) * ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ)) *
        ((fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x) (y' - l • z)
          (coordinateVector k) : ℝ) : ℂ) := by
    funext y'
    unfold sepPhi
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hfun]
  refine (L4_sum _ _ n (fun j _ => ContDiff.sum fun k _ => L4_term_cd _ (hK j) _ _ _) hn y).trans ?_
  refine Finset.sum_le_sum fun j _ => ?_
  refine (L4_sum _ _ n (fun k _ => L4_term_cd _ (hK j) _ _ _) hn y).trans ?_
  refine Finset.sum_le_sum fun k _ => ?_
  exact L4_term _ (hK j) _ _ _ y n hn

lemma L4_varrho_tri (a b : Space) : ϱ a ≤ ϱ (a - b) + ϱ b := by
  have e0 : (a - b) 0 = a 0 - b 0 := rfl
  have e1 : (a - b) 1 = a 1 - b 1 := rfl
  unfold ϱ
  rw [e0, e1]
  set p := a 0 - b 0
  set q := a 1 - b 1
  have hcs : |p * b 0 + q * b 1| ≤ √(p ^ 2 + q ^ 2) * √(b 0 ^ 2 + b 1 ^ 2) := by
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.abs_le_sqrt
    nlinarith [sq_nonneg (p * b 1 - q * b 0)]
  have h1 := Real.sq_sqrt (show 0 ≤ p ^ 2 + q ^ 2 by positivity)
  have h2 := Real.sq_sqrt (show 0 ≤ b 0 ^ 2 + b 1 ^ 2 by positivity)
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  have := (abs_le.1 hcs).2
  have ha : a 0 = p + b 0 := by simp [p]
  have hb : a 1 = q + b 1 := by simp [q]
  rw [ha, hb]
  nlinarith

lemma L4_varrho_le_norm (x : Space) : ϱ x ≤ ‖x‖ := by
  unfold ϱ
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  apply Real.sqrt_le_sqrt
  simp only [Real.norm_eq_abs, sq_abs]
  nlinarith [sq_nonneg (x 2)]

lemma L4_varrho_smul (l : ℝ) (hl : 0 ≤ l) (z : Space) : ϱ (l • z) = l * ϱ z := by
  unfold ϱ
  have : (l • z) 0 ^ 2 + (l • z) 1 ^ 2 = l ^ 2 * (z 0 ^ 2 + z 1 ^ 2) := by
    simp only [PiLp.smul_apply, smul_eq_mul]; ring
  rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq hl]

lemma L4_gap_real (d R s M : ℝ) (hd : 0 < d) (hR : 0 ≤ R) (hs : 0 ≤ s) (hM1 : d ≤ M)
    (hM2 : s - R ≤ M) : d / (1 + R + d) * (1 + s) ≤ M := by
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  by_cases h : s ≤ R + d
  · nlinarith
  · push_neg at h
    nlinarith [mul_nonneg (show 0 ≤ 1 + R by linarith) (show 0 ≤ s - R - d by linarith)]

lemma L4_geom (rOut d ε : ℝ) (y0 y z : Space) (l : ℝ) (hl : l ∈ Ioo (0 : ℝ) 1)
    (hz : ϱ z ≤ rOut) (hy : ‖y - y0‖ < ε) (hεd : ε ≤ d) (hε1 : ε ≤ 1) (hd0 : 0 < d)
    (hd : 2 * d ≤ ϱ y0 - rOut) :
    d / (1 + (‖y0‖ + 1) + d) * (1 + l * ‖z‖) ≤ ‖y - l • z‖ := by
  have h1 : ϱ y0 ≤ ‖y - y0‖ + ϱ y := by
    have := L4_varrho_tri y0 y
    have h' := L4_varrho_le_norm (y0 - y)
    rw [norm_sub_rev] at h'
    linarith
  have h2 : ϱ y ≤ ‖y - l • z‖ + rOut := by
    have := L4_varrho_tri y (l • z)
    have h' := L4_varrho_le_norm (y - l • z)
    rw [L4_varrho_smul l hl.1.le] at this
    have : l * ϱ z ≤ rOut := by
      nlinarith [ϱ_nonneg z, hl.1, hl.2]
    linarith
  have hM1 : d ≤ ‖y - l • z‖ := by linarith
  have hM2 : l * ‖z‖ - (‖y0‖ + 1) ≤ ‖y - l • z‖ := by
    have h3 : ‖l • z‖ - ‖y‖ ≤ ‖l • z - y‖ := norm_sub_norm_le _ _
    rw [norm_sub_rev] at h3
    have h4 : ‖y‖ ≤ ‖y0‖ + ‖y - y0‖ := by
      have := norm_le_norm_add_norm_sub' y y0
      linarith
    rw [norm_smul, Real.norm_of_nonneg hl.1.le] at h3
    linarith
  exact L4_gap_real d (‖y0‖ + 1) (l * ‖z‖) _ hd0 (by positivity) (by have := hl.1; positivity)
    hM1 hM2

lemma L4_entry (M : Matrix (Fin 3) (Fin 3) ℝ) (j k : Fin 3) : |M j k| ≤ IIIa.tensorNorm M := by
  unfold IIIa.tensorNorm
  apply Real.abs_le_sqrt
  have h1 : M j k ^ 2 ≤ ∑ k', M j k' ^ 2 :=
    Finset.single_le_sum (f := fun k' => M j k' ^ 2) (fun _ _ => by positivity) (Finset.mem_univ k)
  have h2 : ∑ k', M j k' ^ 2 ≤ ∑ j', ∑ k', M j' k' ^ 2 :=
    Finset.single_le_sum (f := fun j' => ∑ k', M j' k' ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ j)
  linarith

lemma L4_kern (hK : IIIa.SepKernelBounds) :
    ∃ Cn : ℝ, 0 ≤ Cn ∧ ∀ n : ℕ, n ≤ 2 → ∀ x : Space, x ≠ 0 → ∀ i k : Fin 3, ∀ t : ℝ, 0 < t →
      ‖iteratedFDeriv ℝ (n + 1) (fun y => IIIa.heatLerayK t i k y) x‖ ≤ Cn * ‖x‖ ^ (-4 - (n : ℝ)) := by
  obtain ⟨C0, h0⟩ := hK 0
  obtain ⟨C1, h1⟩ := hK 1
  obtain ⟨C2, h2⟩ := hK 2
  refine ⟨|C0| + |C1| + |C2|, by positivity, ?_⟩
  intro n hn x hx i k t ht
  have hp : 0 ≤ ‖x‖ ^ (-4 - (n : ℝ)) := by positivity
  interval_cases n
  · have := (h0 x hx i k).1 t ht
    refine this.trans (mul_le_mul_of_nonneg_right ?_ hp)
    linarith [le_abs_self C0, abs_nonneg C1, abs_nonneg C2]
  · have := (h1 x hx i k).1 t ht
    refine this.trans (mul_le_mul_of_nonneg_right ?_ hp)
    linarith [le_abs_self C1, abs_nonneg C0, abs_nonneg C2]
  · have := (h2 x hx i k).1 t ht
    refine this.trans (mul_le_mul_of_nonneg_right ?_ hp)
    linarith [le_abs_self C2, abs_nonneg C1, abs_nonneg C0]

lemma L4_majorant_nonneg (μ : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (n : ℕ)
    (l : ℝ) (z : Space) (hl : 0 < l) : 0 ≤ sepMajorant μ T τ n (l, z) := by
  unfold sepMajorant IIIa.tensorNorm
  simp only
  positivity

theorem sepGapPointwise : SepGapPointwise := by
  intro hK ν μ rOut P T hν hμ hr hP hS τ i y0 hy0
  obtain ⟨Cn, hCn0, hCn⟩ := L4_kern hK
  have h2 := heatLerayKSmooth
  set d : ℝ := (ϱ y0 - rOut) / 2 with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  set c : ℝ := d / (1 + (‖y0‖ + 1) + d) with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  have hc1 : c ≤ 1 := by
    rw [hc, div_le_one (by positivity)]; linarith [norm_nonneg y0]
  refine ⟨min d 1, lt_min hd0 one_pos, 18 * Cn * c ^ (-6 : ℝ), by positivity, ?_⟩
  intro y hy l hl z n hn
  have hl0 : 0 < l := hl.1
  by_cases hz : rOut < ϱ z
  · have hT : T (τ + 2 * Real.log l) z = 0 := hS.support _ _ hz
    refine (L4_phi ν μ T τ i l z hl hν h2 n hn y).trans ?_
    have : ∀ j k : Fin 3, ‖(-2 * (l : ℂ) ^ (2 * μ + 2) *
          ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ))‖ = 0 := by
      intro j k; simp [hT]
    simp only [this, zero_mul, Finset.sum_const_zero]
    exact mul_nonneg (by positivity) (L4_majorant_nonneg μ T τ n l z hl0)
  · push Not at hz
    have hyb : ‖y - y0‖ < min d 1 := by simpa [dist_eq_norm] using hy
    have hgeom := L4_geom rOut d (min d 1) y0 y z l hl hz hyb (min_le_left _ _) (min_le_right _ _)
      hd0 (by rw [hd]; linarith)
    have hx0 : 0 < ‖y - l • z‖ := lt_of_lt_of_le (by positivity) hgeom |>.trans_le' le_rfl
    have hx : y - l • z ≠ 0 := norm_pos_iff.1 hx0
    refine (L4_phi ν μ T τ i l z hl hν h2 n hn y).trans ?_
    have hpow : ‖y - l • z‖ ^ (-4 - (n : ℝ)) ≤ c ^ (-6 : ℝ) * (1 + l * ‖z‖) ^ (-(4 + (n : ℝ))) := by
      have h1 : ‖y - l • z‖ ^ (-4 - (n : ℝ)) ≤ (c * (1 + l * ‖z‖)) ^ (-4 - (n : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hgeom (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
      rw [Real.mul_rpow hc0.le (by positivity)] at h1
      have h3 : c ^ (-4 - (n : ℝ)) ≤ c ^ (-6 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hc0 hc1 (by
          have : (n : ℝ) ≤ 2 := by exact_mod_cast hn
          linarith)
      have h4 : (1 + l * ‖z‖) ^ (-4 - (n : ℝ)) = (1 + l * ‖z‖) ^ (-(4 + (n : ℝ))) := by
        congr 1; ring
      rw [h4] at h1
      refine h1.trans (mul_le_mul_of_nonneg_right h3 (by positivity))
    have hterm : ∀ j k : Fin 3, ‖(-2 * (l : ℂ) ^ (2 * μ + 2) *
          ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ))‖ * ‖coordinateVector k‖ *
        ‖iteratedFDeriv ℝ (n + 1) (fun x => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x)
          (y - l • z)‖ ≤ 2 * Cn * c ^ (-6 : ℝ) * sepMajorant μ T τ n (l, z) := by
      intro j k
      have ht : 0 < ν * (1 - l ^ 2) := by
        have := hl.2; nlinarith [mul_pos hν (sub_pos.2 (show l ^ 2 < 1 by nlinarith))]
      have hk := hCn n hn _ hx i j _ ht
      have he : ‖coordinateVector k‖ = 1 := by simp [coordinateVector]
      have hn1 : ‖(-2 * (l : ℂ) ^ (2 * μ + 2) * ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ))‖ ≤
          2 * l ^ (2 * μ.re + 2) * IIIa.tensorNorm (T (τ + 2 * Real.log l) z) := by
        rw [norm_mul, norm_mul, norm_neg, Complex.norm_real,
          Complex.norm_cpow_eq_rpow_re_of_pos hl0]
        simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
          zero_mul, sub_zero, Real.norm_eq_abs]
        have := L4_entry (T (τ + 2 * Real.log l) z) j k
        have hp : 0 ≤ l ^ (2 * μ.re + 2) := by positivity
        have h2' : ‖(2 : ℂ)‖ = 2 := by simp
        rw [h2']
        nlinarith
      rw [he, mul_one]
      have hA : 0 ≤ ‖(-2 * (l : ℂ) ^ (2 * μ + 2) * ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ))‖ :=
        norm_nonneg _
      calc _ ≤ (2 * l ^ (2 * μ.re + 2) * IIIa.tensorNorm (T (τ + 2 * Real.log l) z)) *
            (Cn * (c ^ (-6 : ℝ) * (1 + l * ‖z‖) ^ (-(4 + (n : ℝ))))) := by
            refine mul_le_mul hn1 (hk.trans (mul_le_mul_of_nonneg_left hpow hCn0)) (norm_nonneg _)
              (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
        _ = 2 * Cn * c ^ (-6 : ℝ) * sepMajorant μ T τ n (l, z) := by
            unfold sepMajorant; simp only; ring
    refine (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hterm j k).trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hm := L4_majorant_nonneg μ T τ n l z hl0
    push_cast
    nlinarith

end UnforcedLeray.Short.PartIIIb.Concrete
