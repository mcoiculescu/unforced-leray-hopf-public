import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_7_1_1_1_1_1

/-!
# Part I, `PartI:T02/1/4/4/1/7/1/1/1/1/1/1`: the third-order Taylor remainder

Proves `HeatTaylorRemainder` (see `Sub/PartI_T02_1_4_4_1_7_1_1_1_1_1.lean`): a cylinder-smooth
field has bounded third derivatives, hence the second-order Taylor remainder
`f(x-w) - f x + ∂_w f x - ½ ∂_w² f x` is `O(‖w‖³)` uniformly in `x`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

namespace HeatTaylorRemainderAux

/-- A continuous `c`-periodic (in `q`) field vanishing for `|η|` large is bounded. -/
theorem bdd_of_periodic_support {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {c R : ℝ} (hc : 0 < c) {u : Plane → G} (hcont : Continuous u)
    (hper : ∀ z : Plane, u (z + (c, 0)) = u z)
    (hR : ∀ z : Plane, R < |z.2| → u z = 0) :
    ∃ M : ℝ, ∀ z : Plane, ‖u z‖ ≤ M := by
  have hK : IsCompact (Icc (0:ℝ) c ×ˢ Icc (-(max R 0)) (max R 0)) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 0, fun z => ?_⟩
  by_cases hη : max R 0 < |z.2|
  · have hz : u z = 0 := hR z (lt_of_le_of_lt (le_max_left _ _) hη)
    rw [hz, norm_zero]
    exact le_max_right _ _
  · have hη' : z.2 ∈ Icc (-(max R 0)) (max R 0) := abs_le.mp (not_lt.mp hη)
    have hq : Function.Periodic (fun q : ℝ => u (q, z.2)) c := fun q => by
      simpa [Prod.mk_add_mk] using hper (q, z.2)
    obtain ⟨y, hy, hyeq⟩ := hq.exists_mem_Ico₀ hc z.1
    have hyK : ((y, z.2) : Plane) ∈ Icc (0:ℝ) c ×ˢ Icc (-(max R 0)) (max R 0) :=
      ⟨⟨hy.1, hy.2.le⟩, hη'⟩
    have h1 : ‖u z‖ ≤ C := by
      have e : u z = u (y, z.2) := hyeq
      rw [e]
      exact hC _ hyK
    exact le_trans h1 (le_max_left _ _)

/-- Iterated directional derivatives along a constant vector are the iterated Fréchet
derivative on that vector. -/
theorem iterD_replicate_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (w : Plane) : ∀ (n : ℕ) (φ : Plane → F), ContDiff ℝ ∞ φ → ∀ z : Plane,
      Sob.iterD (List.replicate n w) φ z = iteratedFDeriv ℝ n φ z (fun _ => w)
  | 0, φ, _, z => by simp
  | n + 1, φ, hφ, z => by
    have IH : Sob.iterD (List.replicate n w) φ = fun y => iteratedFDeriv ℝ n φ y (fun _ => w) :=
      funext fun y => iterD_replicate_eq w n φ hφ y
    have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ n φ) z :=
      (hφ.differentiable_iteratedFDeriv (m := n) (by exact_mod_cast ENat.coe_lt_top n)) z
    show fderiv ℝ (Sob.iterD (List.replicate n w) φ) z w = _
    rw [IH]
    exact fderiv_continuousMultilinear_apply_const_apply hdiff (fun _ => w) w

/-- Derivative of the shifted line `s ↦ ∂_{vs} φ (x - s w)`. -/
theorem hasDerivAt_iterD_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : Plane → F} (hφ : ContDiff ℝ ∞ φ) (vs : List Plane) (x w : Plane) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Sob.iterD vs φ (x - s • w))
      (-(Sob.iterD (w :: vs) φ (x - t • w))) t := by
  have hd : DifferentiableAt ℝ (Sob.iterD vs φ) (x - t • w) :=
    ((Sob.contDiff_iterD hφ vs).differentiable (by simp)) _
  have hline : HasDerivAt (fun s : ℝ => x - s • w) (-w) t := by
    have := ((hasDerivAt_id' t).smul_const w).const_sub x
    simpa using this
  have := hd.hasFDerivAt.comp_hasDerivAt t hline
  simpa [Function.comp_def, Sob.iterD_cons, map_neg] using this

/-- Mean value bound on `[0,1]`. -/
theorem mvt01 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f' : ℝ → E} {C : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hb : ∀ x ∈ Icc (0:ℝ) 1, ‖f' x‖ ≤ C) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖f t - f 0‖ ≤ C * |t| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := Icc (0:ℝ) 1) (f := f)
    (f' := f') (C := C) (fun x _ => (hf x).hasDerivWithinAt) hb (convex_Icc 0 1)
    (x := 0) (y := t) ⟨le_refl _, zero_le_one⟩ ht
  simpa [Real.norm_eq_abs] using h

/-- One-dimensional third-order Taylor bound at `0` with the second-order term subtracted. -/
theorem taylor1D {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h0 h1 h2 h3 : ℝ → E) (K : ℝ)
    (d0 : ∀ t, HasDerivAt h0 (-h1 t) t) (d1 : ∀ t, HasDerivAt h1 (-h2 t) t)
    (d2 : ∀ t, HasDerivAt h2 (-h3 t) t) (hK : ∀ t ∈ Icc (0:ℝ) 1, ‖h3 t‖ ≤ K) :
    ‖h0 1 - h0 0 + h1 0 - (1 / 2 : ℝ) • h2 0‖ ≤ K := by
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK 0 ⟨le_refl _, zero_le_one⟩)
  -- step 1: `‖h2 t - h2 0‖ ≤ K` on `[0,1]`
  have s1 : ∀ t ∈ Icc (0:ℝ) 1, ‖h2 t - h2 0‖ ≤ K := by
    intro t ht
    have h := mvt01 (f := h2) (f' := fun x => -h3 x) (C := K) d2
      (fun x hx => by simpa using hK x hx) ht
    have ht1 : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    have := mul_le_mul_of_nonneg_left ht1 hK0
    linarith
  -- step 2: `Q s = h1 s - h1 0 + s • h2 0` satisfies `‖Q t‖ ≤ K` on `[0,1]`
  have dQ : ∀ s : ℝ, HasDerivAt (fun s => h1 s - h1 0 + s • h2 0) (h2 0 - h2 s) s := by
    intro s
    have h := ((d1 s).sub_const (h1 0)).add ((hasDerivAt_id' s).smul_const (h2 0))
    refine h.congr_deriv ?_
    rw [one_smul]
    abel
  have s2 : ∀ t ∈ Icc (0:ℝ) 1, ‖h1 t - h1 0 + t • h2 0‖ ≤ K := by
    intro t ht
    have hb : ∀ x ∈ Icc (0:ℝ) 1, ‖h2 0 - h2 x‖ ≤ K := by
      intro x hx
      rw [norm_sub_rev]
      exact s1 x hx
    have h := mvt01 (f := fun s => h1 s - h1 0 + s • h2 0) (f' := fun x => h2 0 - h2 x)
      (C := K) dQ hb ht
    simp only [zero_smul, sub_self, zero_add, sub_zero] at h
    have ht1 : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    have := mul_le_mul_of_nonneg_left ht1 hK0
    linarith
  -- step 3: `R s = h0 s - h0 0 + s • h1 0 - (s * s / 2) • h2 0` at `s = 1`
  have dR : ∀ s : ℝ, HasDerivAt
      (fun s => h0 s - h0 0 + s • h1 0 - (s * s / 2) • h2 0) (-(h1 s - h1 0 + s • h2 0)) s := by
    intro s
    have hq : HasDerivAt (fun s : ℝ => s * s / 2) s s := by
      have := ((hasDerivAt_id' s).mul (hasDerivAt_id' s)).div_const 2
      refine this.congr_deriv ?_
      ring
    have h := (((d0 s).sub_const (h0 0)).add ((hasDerivAt_id' s).smul_const (h1 0))).sub
      (hq.smul_const (h2 0))
    refine h.congr_deriv ?_
    rw [one_smul]
    module
  have key := mvt01 (f := fun s => h0 s - h0 0 + s • h1 0 - (s * s / 2) • h2 0)
    (f' := fun s => -(h1 s - h1 0 + s • h2 0)) (C := K) dR
    (fun x hx => by rw [norm_neg]; exact s2 x hx) (t := 1) ⟨zero_le_one, le_refl _⟩
  simpa using key

end HeatTaylorRemainderAux

open HeatTaylorRemainderAux

/-- **Leaf A (Taylor; source lines 261-288).** Cylinder-smooth `f` has all derivatives bounded
(periodic with compact transversal support), so `‖R(x,w)‖ ≤ M ‖w‖³` uniformly in `x`. -/
theorem heatTaylorRemainder : HeatTaylorRemainder := by
  intro c hc f hf
  have hcont3 : Continuous (iteratedFDeriv ℝ 3 f) :=
    ContDiff.continuous_iteratedFDeriv (by simp) hf.smooth
  have hper3 : ∀ z : Plane, iteratedFDeriv ℝ 3 f (z + (c, 0)) = iteratedFDeriv ℝ 3 f z := by
    intro z
    have e : (fun y : Plane => f ((c, 0) + y)) = f :=
      funext fun y => by rw [add_comm]; exact hf.periodic y
    have h := iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := f) 3 (c, 0) z
    rw [e] at h
    rw [add_comm]
    exact h.symm
  obtain ⟨R, hR⟩ := hf.bounded
  have hsupp3 : ∀ z : Plane, R < |z.2| → iteratedFDeriv ℝ 3 f z = 0 := by
    intro z hz
    have hopen : IsOpen {y : Plane | R < |y.2|} :=
      isOpen_lt continuous_const (continuous_abs.comp continuous_snd)
    have hev : f =ᶠ[𝓝 z] fun _ => 0 :=
      Filter.eventually_of_mem (hopen.mem_nhds hz) fun y hy => hR y hy
    have h := Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hev 3
    rw [h.eq_of_nhds, iteratedFDeriv_fun_zero]
    simp
  obtain ⟨M3, hM3⟩ := bdd_of_periodic_support (R := R) hc hcont3 hper3 hsupp3
  refine ⟨M3, fun x w => ?_⟩
  have h3 : ∀ t : ℝ, ‖Sob.iterD [w, w, w] f (x - t • w)‖ ≤ M3 * ‖w‖ ^ 3 := by
    intro t
    have e : Sob.iterD [w, w, w] f (x - t • w)
        = iteratedFDeriv ℝ 3 f (x - t • w) (fun _ => w) :=
      iterD_replicate_eq w 3 f hf.smooth (x - t • w)
    rw [e]
    calc ‖iteratedFDeriv ℝ 3 f (x - t • w) (fun _ => w)‖
        ≤ ‖iteratedFDeriv ℝ 3 f (x - t • w)‖ * ∏ _i : Fin 3, ‖w‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ M3 * ∏ _i : Fin 3, ‖w‖ :=
          mul_le_mul_of_nonneg_right (hM3 _) (by positivity)
      _ = M3 * ‖w‖ ^ 3 := by simp
  have hmain := taylor1D (fun t => Sob.iterD [] f (x - t • w))
    (fun t => Sob.iterD [w] f (x - t • w)) (fun t => Sob.iterD [w, w] f (x - t • w))
    (fun t => Sob.iterD [w, w, w] f (x - t • w)) (M3 * ‖w‖ ^ 3)
    (fun t => hasDerivAt_iterD_line hf.smooth [] x w t)
    (fun t => hasDerivAt_iterD_line hf.smooth [w] x w t)
    (fun t => hasDerivAt_iterD_line hf.smooth [w, w] x w t)
    (fun t _ => h3 t)
  unfold heatTaylorR
  simpa [Sob.iterD_nil] using hmain

end UnforcedLeray.Short.PartI

#print axioms UnforcedLeray.Short.PartI.heatTaylorRemainder
