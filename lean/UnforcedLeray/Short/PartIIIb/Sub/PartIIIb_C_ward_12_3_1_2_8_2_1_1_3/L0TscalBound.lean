import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_1_3

/-!
# `PartIII-b:C/ward/12/3/1/2/8/2/1/1/3`: decay of `L0Tscal`

Source `the November 2 reference manuscript`
lines 1393-1400, 1409-1412.  Proves `l0TscalBound`: if `ψ` is smooth with `PotDecay ψ`, then
`σ = L0Tscal ν ψ` satisfies `|σ| ≲ (1+|y|)^{-2}` and `|∇σ| ≲ (1+|y|)^{-3}`.  The derivatives of
`σ` are computed by `HasFDerivAt` calculus; the decay bookkeeping uses the predicate `Dec`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.L0TscalBoundAux

open UnforcedLeray.PhaseSpace

theorem dec_mono {a b : ℝ} (hab : a ≤ b) {ψ : ℝ × UnforcedLeray.Space → ℂ}
    (h : Dec a ψ) : Dec b ψ := by
  unfold Dec at h ⊢
  obtain ⟨C, hC⟩ := h
  refine ⟨|C|, fun τ y => (hC τ y).trans ?_⟩
  have h1 : (0 : ℝ) < 1 + ‖y‖ := by positivity
  have hp : (1 + ‖y‖) ^ a ≤ (1 + ‖y‖) ^ b :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg y]) hab
  have hpos : 0 ≤ (1 + ‖y‖) ^ a := Real.rpow_nonneg h1.le a
  calc C * (1 + ‖y‖) ^ a ≤ |C| * (1 + ‖y‖) ^ a :=
        mul_le_mul_of_nonneg_right (le_abs_self C) hpos
    _ ≤ |C| * (1 + ‖y‖) ^ b := mul_le_mul_of_nonneg_left hp (abs_nonneg C)

theorem dec_add {a : ℝ} {f g : ℝ × UnforcedLeray.Space → ℂ} (hf : Dec a f) (hg : Dec a g) :
    Dec a (fun p => f p + g p) := by
  unfold Dec at hf hg ⊢
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  refine ⟨C + D, fun τ y => ?_⟩
  calc ‖f (τ, y) + g (τ, y)‖ ≤ ‖f (τ, y)‖ + ‖g (τ, y)‖ := norm_add_le _ _
    _ ≤ C * (1 + ‖y‖) ^ a + D * (1 + ‖y‖) ^ a := add_le_add (hC τ y) (hD τ y)
    _ = (C + D) * (1 + ‖y‖) ^ a := by ring

theorem dec_sub {a : ℝ} {f g : ℝ × UnforcedLeray.Space → ℂ} (hf : Dec a f) (hg : Dec a g) :
    Dec a (fun p => f p - g p) := by
  unfold Dec at hf hg ⊢
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  refine ⟨C + D, fun τ y => ?_⟩
  calc ‖f (τ, y) - g (τ, y)‖ ≤ ‖f (τ, y)‖ + ‖g (τ, y)‖ := norm_sub_le _ _
    _ ≤ C * (1 + ‖y‖) ^ a + D * (1 + ‖y‖) ^ a := add_le_add (hC τ y) (hD τ y)
    _ = (C + D) * (1 + ‖y‖) ^ a := by ring

theorem dec_neg {a : ℝ} {f : ℝ × UnforcedLeray.Space → ℂ} (hf : Dec a f) :
    Dec a (fun p => -f p) := by
  unfold Dec at hf ⊢
  obtain ⟨C, hC⟩ := hf
  exact ⟨C, fun τ y => by simpa [norm_neg] using hC τ y⟩

theorem dec_smul {a : ℝ} (c : ℝ) {f : ℝ × UnforcedLeray.Space → ℂ} (hf : Dec a f) :
    Dec a (fun p => c • f p) := by
  unfold Dec at hf ⊢
  obtain ⟨C, hC⟩ := hf
  refine ⟨‖c‖ * C, fun τ y => ?_⟩
  have hpos : 0 ≤ (1 + ‖y‖) ^ a := Real.rpow_nonneg (by positivity) a
  calc ‖c • f (τ, y)‖ = ‖c‖ * ‖f (τ, y)‖ := norm_smul c _
    _ ≤ ‖c‖ * (C * (1 + ‖y‖) ^ a) := mul_le_mul_of_nonneg_left (hC τ y) (norm_nonneg c)
    _ = ‖c‖ * C * (1 + ‖y‖) ^ a := by ring

theorem dec_sum {a : ℝ} {ι : Type*} [Fintype ι] (F : ι → ℝ × UnforcedLeray.Space → ℂ)
    (h : ∀ i, Dec a (F i)) : Dec a (fun p => ∑ i, F i p) := by
  have h' : ∀ i, ∃ C : ℝ, ∀ τ y, ‖F i (τ, y)‖ ≤ C * (1 + ‖y‖) ^ a := fun i => h i
  choose C hC using h'
  refine ⟨∑ i, |C i|, fun τ y => ?_⟩
  have hpos : 0 ≤ (1 + ‖y‖) ^ a := Real.rpow_nonneg (by positivity) a
  calc ‖∑ i, F i (τ, y)‖ ≤ ∑ i, ‖F i (τ, y)‖ := norm_sum_le _ _
    _ ≤ ∑ i, |C i| * (1 + ‖y‖) ^ a := Finset.sum_le_sum fun i _ =>
        (hC i τ y).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hpos)
    _ = (∑ i, |C i|) * (1 + ‖y‖) ^ a := (Finset.sum_mul _ _ _).symm

theorem dec_coord {a b : ℝ} (j : Fin 3) {g : ℝ × UnforcedLeray.Space → ℂ} (hab : a + 1 ≤ b)
    (hg : Dec a g) : Dec b (fun p => (p.2 j) • g p) := by
  refine dec_mono hab ?_
  unfold Dec at hg ⊢
  obtain ⟨C, hC⟩ := hg
  refine ⟨|C|, fun τ y => ?_⟩
  have h0 : (0 : ℝ) < 1 + ‖y‖ := by positivity
  have hpos : 0 ≤ (1 + ‖y‖) ^ a := Real.rpow_nonneg h0.le a
  have h1 : ‖g (τ, y)‖ ≤ |C| * (1 + ‖y‖) ^ a :=
    (hC τ y).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hpos)
  have h2 : |y j| ≤ ‖y‖ := by
    rw [← Real.norm_eq_abs]
    exact PiLp.norm_apply_le y j
  calc ‖(τ, y).2 j • g (τ, y)‖ = |y j| * ‖g (τ, y)‖ := by
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖y‖ * (|C| * (1 + ‖y‖) ^ a) := mul_le_mul h2 h1 (norm_nonneg _) (norm_nonneg _)
    _ ≤ (1 + ‖y‖) * (|C| * (1 + ‖y‖) ^ a) :=
        mul_le_mul_of_nonneg_right (by linarith [norm_nonneg y]) (by positivity)
    _ = |C| * (1 + ‖y‖) ^ (a + 1) := by
        rw [Real.rpow_add_one h0.ne' a]; ring

theorem dec_gradT {a : ℝ} {σ : ℝ × UnforcedLeray.Space → ℂ}
    (h : ∀ k : Fin 3, Dec a (dy k σ)) :
    ∃ C : ℝ, ∀ τ y, ‖gradT σ (τ, y)‖ ≤ C * (1 + ‖y‖) ^ a := by
  have h' : ∀ k : Fin 3, ∃ C : ℝ, ∀ τ y, ‖dy k σ (τ, y)‖ ≤ C * (1 + ‖y‖) ^ a := fun k => h k
  choose C hC using h'
  refine ⟨∑ k, |C k|, fun τ y => ?_⟩
  have hpos : 0 ≤ (1 + ‖y‖) ^ a := Real.rpow_nonneg (by positivity) a
  calc ‖gradT σ (τ, y)‖
      = ‖∑ k : Fin 3, dy k σ (τ, y) • EuclideanSpace.single k (1 : ℂ)‖ := rfl
    _ ≤ ∑ k : Fin 3, ‖dy k σ (τ, y) • EuclideanSpace.single k (1 : ℂ)‖ := norm_sum_le _ _
    _ = ∑ k : Fin 3, ‖dy k σ (τ, y)‖ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [norm_smul, EuclideanSpace.norm_single, norm_one, mul_one]
    _ ≤ ∑ k : Fin 3, |C k| * (1 + ‖y‖) ^ a := Finset.sum_le_sum fun k _ =>
        (hC k τ y).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hpos)
    _ = (∑ k : Fin 3, |C k|) * (1 + ‖y‖) ^ a := (Finset.sum_mul _ _ _).symm

theorem cd_dy {ψ : ℝ × UnforcedLeray.Space → ℂ} (h : ContDiff ℝ ∞ ψ) (j : Fin 3) :
    ContDiff ℝ ∞ (dy j ψ) := by
  unfold dy
  exact (h.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem cd_dτ {ψ : ℝ × UnforcedLeray.Space → ℂ} (h : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (dτ ψ) := by
  unfold dτ
  exact (h.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem cd_radialT {ψ : ℝ × UnforcedLeray.Space → ℂ} (h : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (radialT ψ) := by
  unfold radialT
  exact ContDiff.sum fun j _ => ((contDiff_coord j).comp contDiff_snd).smul (cd_dy h j)

theorem cd_lapT {ψ : ℝ × UnforcedLeray.Space → ℂ} (h : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (lapT ψ) := by
  unfold lapT
  exact ContDiff.sum fun j _ => cd_dy (cd_dy h j) j

/-- `∂_{y_k}` of the `L0Tscal` combination, pointwise. -/
theorem dy_L0Tscal (ν : ℝ) {ψ : ℝ × UnforcedLeray.Space → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (k : Fin 3) (p : ℝ × UnforcedLeray.Space) :
    dy k (L0Tscal ν ψ) p = -(dy k (dτ ψ) p) + (1 / 2 : ℝ) • dy k (radialT ψ) p
      + (1 / 2 : ℝ) • dy k ψ p - ν • dy k (lapT ψ) p := by
  have hA := ((cd_dτ hψ).differentiable (by simp)) p
  have hB := ((cd_radialT hψ).differentiable (by simp)) p
  have hC := (hψ.differentiable (by simp)) p
  have hD := ((cd_lapT hψ).differentiable (by simp)) p
  have hF : HasFDerivAt (L0Tscal ν ψ)
      (-(fderiv ℝ (dτ ψ) p) + (1 / 2 : ℝ) • fderiv ℝ (radialT ψ) p
        + (1 / 2 : ℝ) • fderiv ℝ ψ p - ν • fderiv ℝ (lapT ψ) p) p := by
    have h1 := ((hA.hasFDerivAt.neg.add (hB.hasFDerivAt.const_smul (1 / 2 : ℝ))).add
      (hC.hasFDerivAt.const_smul (1 / 2 : ℝ))).sub (hD.hasFDerivAt.const_smul ν)
    exact h1
  show fderiv ℝ (L0Tscal ν ψ) p (0, coordinateVector k) = _
  rw [hF.fderiv]
  simp [dy]

/-- `∂_{y_k}(y·∇ψ) = ∂_{y_k}ψ + ∑_j y_j ∂_{y_k}∂_{y_j}ψ`, pointwise. -/
theorem dy_radialT_scalar {ψ : ℝ × UnforcedLeray.Space → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (k : Fin 3) (p : ℝ × UnforcedLeray.Space) :
    dy k (radialT ψ) p = ∑ j : Fin 3, ((if j = k then (1 : ℝ) else 0) • dy j ψ p
      + (p.2 j) • dy k (dy j ψ) p) := by
  have hterm : ∀ j : Fin 3, HasFDerivAt (fun q : ℝ × UnforcedLeray.Space => (q.2 j) • dy j ψ q)
      ((p.2 j) • fderiv ℝ (dy j ψ) p + ((EuclideanSpace.proj j : UnforcedLeray.Space →L[ℝ] ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ UnforcedLeray.Space)).smulRight (dy j ψ p)) p := by
    intro j
    have hc := ((EuclideanSpace.proj j : UnforcedLeray.Space →L[ℝ] ℝ).hasFDerivAt).comp p
      (hasFDerivAt_snd)
    exact hc.smul ((cd_dy hψ j).differentiable (by simp) p).hasFDerivAt
  have hRfd : fderiv ℝ (radialT ψ) p = ∑ j : Fin 3, ((p.2 j) • fderiv ℝ (dy j ψ) p
      + ((EuclideanSpace.proj j : UnforcedLeray.Space →L[ℝ] ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ UnforcedLeray.Space)).smulRight (dy j ψ p)) :=
    (HasFDerivAt.fun_sum (fun j _ => hterm j)).fderiv
  show fderiv ℝ (radialT ψ) p (0, coordinateVector k) = _
  rw [hRfd]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [dy, coordinateVector, add_comm]

/-- `∂_{y_k}(Δψ) = ∑_j ∂_{y_k}∂_{y_j}∂_{y_j}ψ`, pointwise. -/
theorem dy_lapT_scalar {ψ : ℝ × UnforcedLeray.Space → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (k : Fin 3) (p : ℝ × UnforcedLeray.Space) :
    dy k (lapT ψ) p = ∑ j : Fin 3, dy k (dy j (dy j ψ)) p := by
  have hterm : ∀ j : Fin 3, HasFDerivAt (fun q : ℝ × UnforcedLeray.Space => dy j (dy j ψ) q)
      (fderiv ℝ (dy j (dy j ψ)) p) p :=
    fun j => ((cd_dy (cd_dy hψ j) j).differentiable (by simp) p).hasFDerivAt
  have hLfd : fderiv ℝ (lapT ψ) p = ∑ j : Fin 3, fderiv ℝ (dy j (dy j ψ)) p :=
    (HasFDerivAt.fun_sum (fun j _ => hterm j)).fderiv
  show fderiv ℝ (lapT ψ) p (0, coordinateVector k) = _
  rw [hLfd]
  simp [dy]

open UnforcedLeray.Short.PartIIIb.Concrete in
theorem l0TscalBoundAux_main : UnforcedLeray.Short.PartIIIb.Concrete.L0TscalBound := by
  intro ν ψ hψ hdec
  unfold PotDecay PotDecay0 at hdec
  obtain ⟨⟨hψ2, hψ3, hψ4, hψ5⟩, h1, h2⟩ := hdec
  -- radial derivative
  have hRad : ∀ k, Dec (-3) (dy k (radialT ψ)) := by
    intro k
    have hfun : dy k (radialT ψ) = fun p => ∑ j : Fin 3,
        ((if j = k then (1 : ℝ) else 0) • dy j ψ p + (p.2 j) • dy k (dy j ψ) p) :=
      funext fun p => dy_radialT_scalar hψ k p
    rw [hfun]
    refine dec_sum _ (fun j => ?_)
    exact dec_add (dec_smul _ (hψ3 j)) (dec_coord j (by norm_num) (hψ4 k j))
  -- Laplacian derivative
  have hLap : ∀ k, Dec (-3) (dy k (lapT ψ)) := by
    intro k
    have hfun : dy k (lapT ψ) = fun p => ∑ j : Fin 3, dy k (dy j (dy j ψ)) p :=
      funext fun p => dy_lapT_scalar hψ k p
    rw [hfun]
    refine dec_sum _ (fun j => ?_)
    exact dec_mono (by norm_num) (hψ5 k j j)
  -- gradient of the correction
  have hSigDy : ∀ k, Dec (-3) (dy k (L0Tscal ν ψ)) := by
    intro k
    have hfun : dy k (L0Tscal ν ψ) = fun p => -(dy k (dτ ψ) p)
        + (1 / 2 : ℝ) • dy k (radialT ψ) p + (1 / 2 : ℝ) • dy k ψ p - ν • dy k (lapT ψ) p :=
      funext fun p => dy_L0Tscal ν hψ k p
    rw [hfun]
    exact dec_sub (dec_add (dec_add (dec_neg (h2 k)) (dec_smul _ (hRad k)))
      (dec_smul _ (hψ3 k))) (dec_smul _ (hLap k))
  -- the value itself
  have hSig : Dec (-2) (L0Tscal ν ψ) := by
    have hrad2 : Dec (-2) (radialT ψ) := by
      unfold radialT
      refine dec_sum _ (fun j => ?_)
      exact dec_coord j (by norm_num) (hψ3 j)
    have hlap2 : Dec (-2) (lapT ψ) := by
      unfold lapT
      refine dec_sum _ (fun j => ?_)
      exact dec_mono (by norm_num) (hψ4 j j)
    unfold L0Tscal
    exact dec_sub (dec_add (dec_add (dec_neg h1) (dec_smul _ hrad2)) (dec_smul _ hψ2))
      (dec_smul _ hlap2)
  unfold Dec at hSig
  obtain ⟨C1, hC1⟩ := hSig
  obtain ⟨C2, hC2⟩ := dec_gradT hSigDy
  refine ⟨|C1| + |C2|, fun τ y => ⟨?_, ?_⟩⟩
  · have hpos : 0 ≤ (1 + ‖y‖) ^ (-2 : ℝ) := Real.rpow_nonneg (by positivity) _
    calc ‖L0Tscal ν ψ (τ, y)‖ ≤ C1 * (1 + ‖y‖) ^ (-2 : ℝ) := hC1 τ y
      _ ≤ |C1| * (1 + ‖y‖) ^ (-2 : ℝ) := mul_le_mul_of_nonneg_right (le_abs_self _) hpos
      _ ≤ (|C1| + |C2|) * (1 + ‖y‖) ^ (-2 : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith [abs_nonneg C2]) hpos
  · have hpos : 0 ≤ (1 + ‖y‖) ^ (-3 : ℝ) := Real.rpow_nonneg (by positivity) _
    calc ‖gradT (L0Tscal ν ψ) (τ, y)‖ ≤ C2 * (1 + ‖y‖) ^ (-3 : ℝ) := hC2 τ y
      _ ≤ |C2| * (1 + ‖y‖) ^ (-3 : ℝ) := mul_le_mul_of_nonneg_right (le_abs_self _) hpos
      _ ≤ (|C1| + |C2|) * (1 + ‖y‖) ^ (-3 : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith [abs_nonneg C1]) hpos

end UnforcedLeray.Short.PartIIIb.Concrete.L0TscalBoundAux

open UnforcedLeray.Short.PartIIIb.Concrete.L0TscalBoundAux in
theorem l0TscalBound : UnforcedLeray.Short.PartIIIb.Concrete.L0TscalBound :=
  l0TscalBoundAux_main
