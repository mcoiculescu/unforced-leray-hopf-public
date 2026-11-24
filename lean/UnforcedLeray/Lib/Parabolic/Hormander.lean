import UnforcedLeray.Lib.Parabolic.Kernel
import UnforcedLeray.Lib.CZCore.CZWeak

/-!
# The causal heat Hessian kernel: size and Hörmander bounds in the CZ core (INF02 T5, part 2)


target T5 (`causalKernel_hormander`) and §4 BP-B step 4; decision D4 of `scoping/README.md` §3:
INF02 uses the parabolic instance, weights `(2,1,…,1)`, of the anisotropic Calderón–Zygmund
core `Lib/CZCore` (whose gauge is `ρ(v) = max(|v₀|^{1/2}, |v₁|, …, |v_d|)` on `ℝ^{1+d}`).

Manuscript: eq:free-stress-11 (`paper/main.tex` lines 7447–7477, blueprint unit B0423), applied
to the kernel `1_{θ>0}∂_{ij}H_θ` with dilation weights `(1,…,1,2)` (line 7466).

* `parWeights d = (2,1,…,1)`, `homDim_parWeights : homDim = d + 2`.
* `psEquiv d : (Fin (d+1) → ℝ) ≃ᵐ ℝ × ℝ^d`, `v ↦ (v₀, (v_{j+1})_j)`, measure preserving
  (`measurePreserving_psEquiv`), additive (`psEquiv_sub`, `psEquiv_neg`), continuous.
* `sq_anisoNorm_le`: `ρ(v)² ≤ |t| + |x|²` for `(t,x) = psEquiv v`; `norm_snd_psEquiv_le`:
  `|x| ≤ √d ρ(v)`.
* `abs_causalKernel_psEquiv_le` (**size**): `|K(psEquiv v)| ≤ C ρ(v)^{-(d+2)}` for `v ≠ 0`.
* `hormander_causalKernel_psEquiv` (**Hörmander**): `∫_{ρ(v) > 2ρ(w)} |K(v - w) - K(v)| ≤ B`
  for the transported kernel, uniformly in `w`; `hormander_comp_neg` gives the same for the
  reflected kernel `v ↦ K(-v)` (the kernel of the transpose).
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Parabolic

open MeasureTheory Real Set
open scoped ENNReal NNReal

open UnforcedLeray.Gaussian (Euc gaussKernel)
open UnforcedLeray.CZ (anisoNorm homDim)

variable {d : ℕ}

instance instIsAddHaarMeasurePS : (volume : Measure (PS d)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure volume volume

/-- The parabolic weights `(2,1,…,1)` on `ℝ^{1+d}` (time first). -/
def parWeights (d : ℕ) : Fin (d + 1) → ℕ+ := Fin.cons 2 (fun _ => 1)

@[simp] theorem parWeights_zero : parWeights d 0 = 2 := rfl

@[simp] theorem parWeights_succ (j : Fin d) : parWeights d j.succ = 1 := rfl

theorem homDim_parWeights : homDim (parWeights d) = d + 2 := by
  simp [homDim, Fin.sum_univ_succ, parWeights]
  ring

/-- Coordinates `ℝ^{1+d} ≃ ℝ × ℝ^d`, `v ↦ (v₀, (v_{j+1})_j)`. -/
def psEquiv (d : ℕ) : (Fin (d + 1) → ℝ) ≃ᵐ PS d :=
  (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.toLp 2 (Fin d → ℝ)))

theorem psEquiv_apply (v : Fin (d + 1) → ℝ) :
    psEquiv d v = (v 0, WithLp.toLp 2 (fun j => v j.succ)) := by
  simp [psEquiv, MeasurableEquiv.piFinSuccAbove_apply]
  rfl

@[simp] theorem psEquiv_fst (v : Fin (d + 1) → ℝ) : (psEquiv d v).1 = v 0 := by
  rw [psEquiv_apply]

@[simp] theorem psEquiv_snd_apply (v : Fin (d + 1) → ℝ) (j : Fin d) :
    (psEquiv d v).2.ofLp j = v j.succ := by
  rw [psEquiv_apply]

theorem measurePreserving_psEquiv : MeasurePreserving (psEquiv d) volume volume := by
  have h1 := measurePreserving_piFinSuccAbove (fun _ : Fin (d + 1) => (volume : Measure ℝ)) 0
  have h2 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin d → ℝ)) volume volume := by
    have := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).symm
    simpa using this
  have h3 := (MeasurePreserving.id (volume : Measure ℝ)).prod h2
  exact h3.comp h1

theorem psEquiv_sub (v w : Fin (d + 1) → ℝ) : psEquiv d (v - w) = psEquiv d v - psEquiv d w := by
  ext1
  · simp
  · ext j; simp

theorem psEquiv_neg (v : Fin (d + 1) → ℝ) : psEquiv d (-v) = -psEquiv d v := by
  ext1
  · simp
  · ext j; simp

theorem continuous_psEquiv : Continuous (psEquiv d) := by
  have : (psEquiv d : (Fin (d + 1) → ℝ) → PS d) =
      fun v => (v 0, WithLp.toLp 2 (fun j => v j.succ)) := funext psEquiv_apply
  rw [this]
  exact (continuous_apply 0).prodMk
    ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => continuous_apply j.succ))

theorem continuous_psEquiv_symm : Continuous (psEquiv d).symm := by
  have h : ((psEquiv d).symm : PS d → Fin (d + 1) → ℝ) =
      fun X : PS d => (Fin.cons X.1 (fun j => X.2.ofLp j) : Fin (d + 1) → ℝ) := by
    funext X
    apply (psEquiv d).injective
    rw [MeasurableEquiv.apply_symm_apply, psEquiv_apply]
    ext <;> simp
  rw [h]
  refine continuous_pi fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using continuous_fst
  · simp only [Fin.cons_succ]
    exact (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) j).comp continuous_snd

/-- The homeomorphism underlying `psEquiv`. -/
def psHomeomorph (d : ℕ) : (Fin (d + 1) → ℝ) ≃ₜ PS d where
  toEquiv := (psEquiv d).toEquiv
  continuous_toFun := continuous_psEquiv
  continuous_invFun := continuous_psEquiv_symm

section Gauge

theorem abs_fst_psEquiv_le (v : Fin (d + 1) → ℝ) :
    |(psEquiv d v).1| ≤ anisoNorm (parWeights d) v ^ 2 := by
  rw [psEquiv_fst]
  simpa using UnforcedLeray.CZ.abs_le_anisoNorm_pow (parWeights d) v 0

theorem norm_snd_psEquiv_le (v : Fin (d + 1) → ℝ) :
    ‖(psEquiv d v).2‖ ≤ Real.sqrt d * anisoNorm (parWeights d) v := by
  set A := anisoNorm (parWeights d) v
  have hA : 0 ≤ A := UnforcedLeray.CZ.anisoNorm_nonneg _ v
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq hA, ← Real.sqrt_mul (Nat.cast_nonneg d)]
  refine Real.sqrt_le_sqrt ?_
  have hj : ∀ j : Fin d, ‖(psEquiv d v).2.ofLp j‖ ^ 2 ≤ A ^ 2 := by
    intro j
    have h := UnforcedLeray.CZ.abs_le_anisoNorm_pow (parWeights d) v j.succ
    simp only [parWeights_succ, PNat.one_coe, pow_one] at h
    rw [psEquiv_snd_apply, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  calc ∑ j, ‖(psEquiv d v).2.ofLp j‖ ^ 2 ≤ ∑ _j : Fin d, A ^ 2 := Finset.sum_le_sum fun j _ => hj j
    _ = d * A ^ 2 := by simp

/-- `ρ(v)² ≤ |t| + |x|²` for `(t, x) = psEquiv v`. -/
theorem sq_anisoNorm_le (v : Fin (d + 1) → ℝ) :
    anisoNorm (parWeights d) v ^ 2 ≤ |(psEquiv d v).1| + ‖(psEquiv d v).2‖ ^ 2 := by
  set r := Real.sqrt (|(psEquiv d v).1| + ‖(psEquiv d v).2‖ ^ 2)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = |(psEquiv d v).1| + ‖(psEquiv d v).2‖ ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hle : anisoNorm (parWeights d) v ≤ r := by
    rw [UnforcedLeray.CZ.anisoNorm_le_iff_abs _ hr]
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [parWeights_zero, PNat.val_ofNat]
      rw [hr2, ← psEquiv_fst v]
      linarith [sq_nonneg ‖(psEquiv d v).2‖]
    · simp only [parWeights_succ, PNat.one_coe, pow_one]
      have h1 : |v j.succ| ≤ ‖(psEquiv d v).2‖ := by
        rw [← psEquiv_snd_apply v j, ← Real.norm_eq_abs]
        exact PiLp.norm_apply_le _ j
      refine h1.trans ?_
      exact Real.le_sqrt_of_sq_le (by linarith [abs_nonneg (psEquiv d v).1])
  rw [← hr2]
  exact pow_le_pow_left₀ (UnforcedLeray.CZ.anisoNorm_nonneg _ v) hle 2

/-- Monotonicity of the gauge under coordinatewise domination. -/
theorem anisoNorm_le_of_abs_le {N : ℕ} (a : Fin N → ℕ+) {u w : Fin N → ℝ}
    (h : ∀ i, |u i| ≤ |w i|) : anisoNorm a u ≤ anisoNorm a w := by
  rw [UnforcedLeray.CZ.anisoNorm_le_iff_abs a (UnforcedLeray.CZ.anisoNorm_nonneg a w)]
  exact fun i => (h i).trans (UnforcedLeray.CZ.abs_le_anisoNorm_pow a w i)

end Gauge

/-- The transported kernel `K ∘ psEquiv` on `ℝ^{1+d}`. -/
def causalKernelCoord (i j : Fin d) (v : Fin (d + 1) → ℝ) : ℝ := causalKernel i j (psEquiv d v)

theorem measurable_causalKernelCoord (i j : Fin d) : Measurable (causalKernelCoord i j) :=
  (measurable_causalKernel i j).comp (psEquiv d).measurable

section Size

/-- **Size bound** in the gauge of the core: `|K(psEquiv v)| ≤ C ρ(v)^{-(d+2)}`, `v ≠ 0`. -/
theorem abs_causalKernelCoord_le (i j : Fin d) : ∃ C : ℝ, 0 < C ∧ ∀ v : Fin (d + 1) → ℝ, v ≠ 0 →
    |causalKernelCoord i j v| ≤ C * anisoNorm (parWeights d) v ^ (-((d : ℝ) + 2)) := by
  obtain ⟨C, hC, h⟩ := abs_hessG_le (d := d) i j
  refine ⟨C, hC, fun v hv => ?_⟩
  have hA : 0 < anisoNorm (parWeights d) v := UnforcedLeray.CZ.anisoNorm_pos _ hv
  unfold causalKernelCoord causalKernel
  split_ifs with ht
  · refine (h ht _).trans ?_
    have h1 := sq_anisoNorm_le v
    rw [abs_of_pos ht] at h1
    have hexp : -(((d : ℝ) + 2) / 2) ≤ 0 := by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith
    have h2 : ((psEquiv d v).1 + ‖(psEquiv d v).2‖ ^ 2) ^ (-(((d : ℝ) + 2) / 2)) ≤
        (anisoNorm (parWeights d) v ^ 2) ^ (-(((d : ℝ) + 2) / 2)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) h1 hexp
    have h3 : (anisoNorm (parWeights d) v ^ 2) ^ (-(((d : ℝ) + 2) / 2)) =
        anisoNorm (parWeights d) v ^ (-((d : ℝ) + 2)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hA.le]; congr 1; push_cast; ring
    rw [h3] at h2
    exact mul_le_mul_of_nonneg_left h2 hC.le
  · simp only [abs_zero]
    positivity

end Size

section HormanderIntegral

/-- A tail integral: `∫_{ρ > 2a} c a^k ρ^{-(d+2+k)} ≤ c M_k 2^{-k}` with
`M_k = 2^{d+1} 2^{d+2} / (1 - 2^{-k})`. -/
theorem lintegral_far_rpow_le (k : ℕ) (hk : 0 < k) {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) :
    ∫⁻ v in {v : Fin (d + 1) → ℝ | 2 * a < anisoNorm (parWeights d) v},
        ENNReal.ofReal (c * a ^ k * anisoNorm (parWeights d) v ^ (-((d : ℝ) + 2 + k))) ≤
      ENNReal.ofReal (c * (2 ^ (d + 1) * 2 ^ (d + 2) / (1 - 2 ^ (-(k : ℝ)))) *
        2 ^ (-(k : ℝ))) := by
  have hb : ((homDim (parWeights d) : ℕ) : ℝ) < (d : ℝ) + 2 + k := by
    rw [homDim_parWeights]; push_cast
    have : (0 : ℝ) < k := by exact_mod_cast hk
    linarith
  have htail := UnforcedLeray.CZ.lintegral_anisoNorm_rpow_neg_le (parWeights d) hb
    (by positivity : (0 : ℝ) < 2 * a)
  have hrw : ∀ v : Fin (d + 1) → ℝ,
      ENNReal.ofReal (c * a ^ k * anisoNorm (parWeights d) v ^ (-((d : ℝ) + 2 + k))) =
        ENNReal.ofReal (c * a ^ k) *
          ENNReal.ofReal (anisoNorm (parWeights d) v ^ (-((d : ℝ) + 2 + k))) := fun v =>
    ENNReal.ofReal_mul (by positivity)
  simp_rw [hrw]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (mul_le_mul_of_nonneg_left htail (zero_le)).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [homDim_parWeights]
  have hexp : (((d + 2 : ℕ) : ℝ) - ((d : ℝ) + 2 + k)) = -(k : ℝ) := by push_cast; ring
  rw [hexp, Real.mul_rpow (by norm_num) ha.le, Real.rpow_neg ha.le, Real.rpow_natCast]
  have hak : a ^ k * (a ^ k)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ ha.ne')
  calc _ = c * (2 ^ (d + 1) * 2 ^ (d + 2) / (1 - 2 ^ (-(k : ℝ)))) * 2 ^ (-(k : ℝ)) *
        (a ^ k * (a ^ k)⁻¹) := by ring
    _ = _ := by rw [hak, mul_one]

theorem one_sub_two_rpow_neg_pos (k : ℕ) (hk : 0 < k) : 0 < 1 - (2 : ℝ) ^ (-(k : ℝ)) := by
  rw [sub_pos]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    linarith)

/-- The Hörmander constant of the transported kernel (as a real number). -/
def hormConstReal (d : ℕ) (C₁ C₂ : ℝ) : ℝ :=
  (C₁ * Real.sqrt d * 2 ^ (d + 3)) *
      (2 ^ (d + 1) * 2 ^ (d + 2) / (1 - 2 ^ (-((1 : ℕ) : ℝ)))) * 2 ^ (-((1 : ℕ) : ℝ)) +
    (C₂ * 2 ^ (d + 4)) *
      (2 ^ (d + 1) * 2 ^ (d + 2) / (1 - 2 ^ (-((2 : ℕ) : ℝ)))) * 2 ^ (-((2 : ℕ) : ℝ))

/-- `((A/2)²)^{-b/2} = 2^b A^{-b}`. -/
theorem half_sq_rpow {A : ℝ} (hA : 0 < A) (b : ℝ) :
    ((A / 2) ^ 2) ^ (-(b / 2)) = 2 ^ b * A ^ (-b) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.div_rpow hA.le (by norm_num)]
  rw [show ((2 : ℕ) : ℝ) * -(b / 2) = -b by push_cast; ring, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  field_simp

/-- **INF02 T5: Hörmander condition** for the transported causal kernel: for every `w`,
`∫_{ρ(v) > 2ρ(w)} |K(v - w) - K(v)| dv ≤ B`, with `B` independent of `w`. -/
theorem hormander_causalKernelCoord (i j : Fin d) : ∃ B : ℝ≥0, ∀ w : Fin (d + 1) → ℝ,
    ∫⁻ v in {v | 2 * anisoNorm (parWeights d) w < anisoNorm (parWeights d) v},
      ‖causalKernelCoord i j (v - w) - causalKernelCoord i j v‖ₑ ≤ B := by
  obtain ⟨C₁, C₂, hC₁, hC₂, h⟩ := abs_causalKernel_sub_le (d := d) i j
  refine ⟨(hormConstReal d C₁ C₂).toNNReal, fun w => ?_⟩
  set ρ := anisoNorm (parWeights d)
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  have hρw : 0 < ρ w := UnforcedLeray.CZ.anisoNorm_pos _ hw
  -- pointwise bound
  have hpt : ∀ v ∈ {v | 2 * ρ w < ρ v},
      ‖causalKernelCoord i j (v - w) - causalKernelCoord i j v‖ₑ ≤
        ENNReal.ofReal ((C₁ * Real.sqrt d * 2 ^ (d + 3)) * ρ w ^ 1 *
            ρ v ^ (-((d : ℝ) + 2 + (1 : ℕ)))) +
          ENNReal.ofReal ((C₂ * 2 ^ (d + 4)) * ρ w ^ 2 * ρ v ^ (-((d : ℝ) + 2 + (2 : ℕ)))) := by
    intro v hv
    simp only [mem_ofPred_eq] at hv
    have hρv : 0 < ρ v := hρw.trans (by linarith)
    set R := (ρ v / 2) ^ 2 with hR
    have hRpos : 0 < R := by positivity
    have hhalf : ρ v / 2 ≤ ρ v - ρ w := by linarith
    -- lower bound along any path point `u` with `|v - u| ≤ |w|` coordinatewise
    have hlow : ∀ u : Fin (d + 1) → ℝ, (∀ k, |(v - u) k| ≤ |w k|) →
        R ≤ |(psEquiv d u).1| + ‖(psEquiv d u).2‖ ^ 2 := by
      intro u hu
      have h1 : ρ (v - u) ≤ ρ w := anisoNorm_le_of_abs_le _ hu
      have h2 : ρ v ≤ ρ u + ρ (v - u) := by
        have := UnforcedLeray.CZ.anisoNorm_add_le (parWeights d) u (v - u)
        rwa [add_sub_cancel] at this
      have h3 : ρ v / 2 ≤ ρ u := by linarith
      calc R = (ρ v / 2) ^ 2 := rfl
        _ ≤ ρ u ^ 2 := pow_le_pow_left₀ (by positivity) h3 2
        _ ≤ _ := sq_anisoNorm_le u
    have hX := h (psEquiv d v) (psEquiv d w) hRpos ?_ ?_
    · rw [causalKernelCoord, causalKernelCoord, psEquiv_sub]
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal (hX.trans ?_)
      have hs : |(psEquiv d w).1| ≤ ρ w ^ 2 := abs_fst_psEquiv_le w
      have hy : ‖(psEquiv d w).2‖ ≤ Real.sqrt d * ρ w := norm_snd_psEquiv_le w
      rw [hR, half_sq_rpow hρv, half_sq_rpow hρv]
      have p3 : (2 : ℝ) ^ ((d : ℝ) + 3) = 2 ^ (d + 3) := by norm_cast
      have p4 : (2 : ℝ) ^ ((d : ℝ) + 4) = 2 ^ (d + 4) := by norm_cast
      have e1 : -((d : ℝ) + 2 + ((1 : ℕ) : ℝ)) = -((d : ℝ) + 3) := by push_cast; ring
      have e2 : -((d : ℝ) + 2 + ((2 : ℕ) : ℝ)) = -((d : ℝ) + 4) := by push_cast; ring
      rw [p3, p4, e1, e2]
      have hv3 : 0 ≤ ρ v ^ (-((d : ℝ) + 3)) := (Real.rpow_pos_of_pos hρv _).le
      have hv4 : 0 ≤ ρ v ^ (-((d : ℝ) + 4)) := (Real.rpow_pos_of_pos hρv _).le
      calc C₁ * ‖(psEquiv d w).2‖ * (2 ^ (d + 3) * ρ v ^ (-((d : ℝ) + 3))) +
            C₂ * |(psEquiv d w).1| * (2 ^ (d + 4) * ρ v ^ (-((d : ℝ) + 4)))
          ≤ C₁ * (Real.sqrt d * ρ w) * (2 ^ (d + 3) * ρ v ^ (-((d : ℝ) + 3))) +
            C₂ * ρ w ^ 2 * (2 ^ (d + 4) * ρ v ^ (-((d : ℝ) + 4))) := by gcongr
        _ = C₁ * Real.sqrt d * 2 ^ (d + 3) * ρ w ^ 1 * ρ v ^ (-((d : ℝ) + 3)) +
            C₂ * 2 ^ (d + 4) * ρ w ^ 2 * ρ v ^ (-((d : ℝ) + 4)) := by ring
    · -- time path
      intro τ hτ
      set u : Fin (d + 1) → ℝ := Fin.cons τ (fun k => v k.succ) with hu
      have hpu : psEquiv d u = (τ, (psEquiv d v).2) := by
        ext1
        · simp [hu]
        · ext k; simp [hu]
      have := hlow u (fun k => by
        refine Fin.cases ?_ (fun m => ?_) k
        · simp only [hu, Pi.sub_apply, Fin.cons_zero]
          rw [psEquiv_fst, psEquiv_fst] at hτ
          have := Set.abs_sub_right_of_mem_uIcc hτ
          rwa [show v 0 - (v 0 - w 0) = w 0 by ring] at this
        · simp [hu])
      rwa [hpu] at this
    · -- space path
      intro θ hθ
      set u : Fin (d + 1) → ℝ := Fin.cons (v 0 - w 0) (fun k => v k.succ - θ * w k.succ) with hu
      have hpu : psEquiv d u = ((psEquiv d v).1 - (psEquiv d w).1,
          (psEquiv d v).2 - θ • (psEquiv d w).2) := by
        ext1
        · simp [hu]
        · ext k; simp [hu]
      have := hlow u (fun k => by
        refine Fin.cases ?_ (fun m => ?_) k
        · simp [hu]
        · simp only [hu, Pi.sub_apply, Fin.cons_succ]
          rw [show v m.succ - (v m.succ - θ * w m.succ) = θ * w m.succ by ring, abs_mul,
            abs_of_nonneg hθ.1]
          exact mul_le_of_le_one_left (abs_nonneg _) hθ.2)
      rw [hpu] at this
      exact this
  -- integrate
  have hmeas : MeasurableSet {v : Fin (d + 1) → ℝ | 2 * ρ w < ρ v} :=
    measurableSet_lt measurable_const (UnforcedLeray.CZ.measurable_anisoNorm _)
  calc ∫⁻ v in {v | 2 * ρ w < ρ v}, ‖causalKernelCoord i j (v - w) - causalKernelCoord i j v‖ₑ
      ≤ ∫⁻ v in {v | 2 * ρ w < ρ v},
          (ENNReal.ofReal ((C₁ * Real.sqrt d * 2 ^ (d + 3)) * ρ w ^ 1 *
              ρ v ^ (-((d : ℝ) + 2 + (1 : ℕ)))) +
            ENNReal.ofReal ((C₂ * 2 ^ (d + 4)) * ρ w ^ 2 *
              ρ v ^ (-((d : ℝ) + 2 + (2 : ℕ))))) := setLIntegral_mono' hmeas hpt
    _ ≤ ENNReal.ofReal ((C₁ * Real.sqrt d * 2 ^ (d + 3)) *
            (2 ^ (d + 1) * 2 ^ (d + 2) / (1 - 2 ^ (-((1 : ℕ) : ℝ)))) * 2 ^ (-((1 : ℕ) : ℝ))) +
          ENNReal.ofReal ((C₂ * 2 ^ (d + 4)) *
            (2 ^ (d + 1) * 2 ^ (d + 2) / (1 - 2 ^ (-((2 : ℕ) : ℝ)))) * 2 ^ (-((2 : ℕ) : ℝ))) := by
        rw [lintegral_add_left]
        · exact add_le_add (lintegral_far_rpow_le 1 one_pos hρw (by positivity))
            (lintegral_far_rpow_le 2 two_pos hρw (by positivity))
        · exact (((measurable_const.mul ((UnforcedLeray.CZ.measurable_anisoNorm _).pow_const _))).ennreal_ofReal)
    _ = ENNReal.ofReal (hormConstReal d C₁ C₂) := by
        have h1 := one_sub_two_rpow_neg_pos 1 one_pos
        have h2 := one_sub_two_rpow_neg_pos 2 two_pos
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        rfl
    _ = ((hormConstReal d C₁ C₂).toNNReal : ℝ≥0∞) := by rw [ENNReal.ofReal]

/-- Hörmander's condition passes to the reflected kernel `v ↦ K(-v)` (the transpose). -/
theorem hormander_comp_neg {N : ℕ} (a : Fin N → ℕ+) {K : (Fin N → ℝ) → ℝ} {B : ℝ≥0}
    (hK : ∀ w, ∫⁻ v in {v | 2 * anisoNorm a w < anisoNorm a v}, ‖K (v - w) - K v‖ₑ ≤ B) :
    ∀ w, ∫⁻ v in {v | 2 * anisoNorm a w < anisoNorm a v}, ‖K (-(v - w)) - K (-v)‖ₑ ≤ B := by
  intro w
  have hneg : MeasurePreserving (fun v : Fin N → ℝ => -v) volume volume :=
    Measure.measurePreserving_neg volume
  have hemb : MeasurableEmbedding (fun v : Fin N → ℝ => -v) :=
    (Homeomorph.neg (Fin N → ℝ)).measurableEmbedding
  have := hneg.setLIntegral_comp_preimage_emb hemb
    (fun v => ‖K (v - -w) - K v‖ₑ) {v | 2 * anisoNorm a (-w) < anisoNorm a v}
  have hset : (fun v : Fin N → ℝ => -v) ⁻¹' {v | 2 * anisoNorm a (-w) < anisoNorm a v} =
      {v | 2 * anisoNorm a w < anisoNorm a v} := by
    ext v; simp [UnforcedLeray.CZ.anisoNorm_neg]
  rw [hset] at this
  calc ∫⁻ v in {v | 2 * anisoNorm a w < anisoNorm a v}, ‖K (-(v - w)) - K (-v)‖ₑ
      = ∫⁻ v in {v | 2 * anisoNorm a w < anisoNorm a v}, ‖K (-v - -w) - K (-v)‖ₑ := by
        congr 1; funext v; congr 3; abel
    _ = _ := this
    _ ≤ B := hK (-w)

end HormanderIntegral

end UnforcedLeray.Parabolic
