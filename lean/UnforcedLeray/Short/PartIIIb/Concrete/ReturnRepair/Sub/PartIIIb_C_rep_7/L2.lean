import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_7
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.StreamCut

/-!
# `streamCutThird` (PartIII-b:C/rep/7/2, source 4178-4186, 4917-4937, 5449-5458)

The third-derivative companion of `StreamCutJet`.  From `SCXJet` (`‖∂^m X(y)‖ ≤ C₄ B r^{-4-m}`,
`m ≤ 7`, `X = 𝒞_yZ`) at `m = 3`: `D(Δ X)(y)[e_k] = Σ_j D³X(y)[e_k,e_j,e_j]`, so each entry is
bounded by `3‖D³X(y)‖` and the Frobenius norm by `9‖D³X(y)‖ ≤ 9 C₄ B r^{-7}`, `r = s^{-1/2}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace StreamThird

variable {X : Vec3 → Vec3}

theorem hasFDeriv_app {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : F → (E →L[ℝ] G)} {y : F} (hg : DifferentiableAt ℝ g y) (a : E) :
    HasFDerivAt (fun y' => g y' a)
      ((ContinuousLinearMap.apply ℝ G a).comp (fderiv ℝ g y)) y :=
  (ContinuousLinearMap.apply ℝ G a).hasFDerivAt.comp y hg.hasFDerivAt

theorem norm_single_le (j : Fin 3) : ‖(Pi.single j (1 : ℝ) : Vec3)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  by_cases h : i = j
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

/-- Local form of `vecLap` near a `C^3` point. -/
theorem vecLap_nhds {y₀ : Vec3} (hX : ContDiffAt ℝ 3 X y₀) :
    vecLap X =ᶠ[nhds y₀] fun y => ∑ j : Fin 3,
      fderiv ℝ (fderiv ℝ X) y (Pi.single j 1) (Pi.single j 1) := by
  filter_upwards [hX.eventually (by simp)] with y hy
  unfold vecLap
  refine Finset.sum_congr rfl fun j _ => ?_
  have hd : DifferentiableAt ℝ (fderiv ℝ X) y :=
    (hy.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  rw [(hasFDeriv_app hd (Pi.single j 1)).fderiv]; rfl

theorem fderiv_vecLap_apply {y₀ : Vec3} (hX : ContDiffAt ℝ 3 X y₀) (v : Vec3) :
    fderiv ℝ (vecLap X) y₀ v = ∑ j : Fin 3,
      fderiv ℝ (fderiv ℝ (fderiv ℝ X)) y₀ v (Pi.single j 1) (Pi.single j 1) := by
  rw [(vecLap_nhds hX).fderiv_eq]
  have h2 : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ X)) y₀ :=
    (hX.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)
  have hd : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ X)) y₀ := h2.differentiableAt (by norm_num)
  have hterm : ∀ j : Fin 3, HasFDerivAt
      (fun y => fderiv ℝ (fderiv ℝ X) y (Pi.single j 1) (Pi.single j 1))
      ((ContinuousLinearMap.apply ℝ Vec3 (Pi.single j 1)).comp
        ((ContinuousLinearMap.apply ℝ (Vec3 →L[ℝ] Vec3) (Pi.single j 1)).comp
          (fderiv ℝ (fderiv ℝ (fderiv ℝ X)) y₀))) y₀ := by
    intro j
    exact (ContinuousLinearMap.apply ℝ Vec3 (Pi.single j 1)).hasFDerivAt.comp y₀
      (hasFDeriv_app hd (Pi.single j 1))
  have hsum := HasFDerivAt.sum (u := Finset.univ) fun j _ => hterm j
  have e : (fun y => ∑ j : Fin 3, fderiv ℝ (fderiv ℝ X) y (Pi.single j 1) (Pi.single j 1)) =
      ∑ j : Fin 3, fun y => fderiv ℝ (fderiv ℝ X) y (Pi.single j 1) (Pi.single j 1) := by
    funext y; simp
  rw [e, hsum.fderiv]
  simp

theorem third_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (y a b c : E) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) y a b c‖ ≤ ‖iteratedFDeriv ℝ 3 f y‖ * ‖a‖ * ‖b‖ * ‖c‖ := by
  have hT : ‖iteratedFDeriv ℝ 1 (fderiv ℝ (fderiv ℝ f)) y‖ = ‖iteratedFDeriv ℝ 3 f y‖ := by
    rw [norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv]
  have ha : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) y a‖ ≤ ‖iteratedFDeriv ℝ 3 f y‖ * ‖a‖ := by
    have := (iteratedFDeriv ℝ 1 (fderiv ℝ (fderiv ℝ f)) y).le_opNorm (fun _ => a)
    rw [iteratedFDeriv_one_apply] at this
    simpa [hT] using this
  calc ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) y a b c‖
      ≤ ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) y a b‖ * ‖c‖ := (_ : E →L[ℝ] F).le_opNorm _
    _ ≤ ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) y a‖ * ‖b‖ * ‖c‖ := by
        gcongr; exact (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) y a).le_opNorm _
    _ ≤ ‖iteratedFDeriv ℝ 3 f y‖ * ‖a‖ * ‖b‖ * ‖c‖ := by gcongr

theorem entry_le {y₀ : Vec3} (hX : ContDiffAt ℝ 3 X y₀) (i k : Fin 3) :
    |fderiv ℝ (vecLap X) y₀ (Pi.single k 1) i| ≤ 3 * ‖iteratedFDeriv ℝ 3 X y₀‖ := by
  rw [fderiv_vecLap_apply hX, Finset.sum_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hj : ∀ j : Fin 3, |fderiv ℝ (fderiv ℝ (fderiv ℝ X)) y₀ (Pi.single k 1) (Pi.single j 1)
      (Pi.single j 1) i| ≤ ‖iteratedFDeriv ℝ 3 X y₀‖ := by
    intro j
    have h1 : |fderiv ℝ (fderiv ℝ (fderiv ℝ X)) y₀ (Pi.single k 1) (Pi.single j 1)
        (Pi.single j 1) i| ≤
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ X)) y₀ (Pi.single k 1) (Pi.single j 1) (Pi.single j 1)‖ := by
      rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ i
    refine h1.trans ((third_le X y₀ _ _ _).trans ?_)
    have := norm_single_le k
    have := norm_single_le j
    have h0 : 0 ≤ ‖iteratedFDeriv ℝ 3 X y₀‖ := norm_nonneg _
    calc ‖iteratedFDeriv ℝ 3 X y₀‖ * ‖(Pi.single k 1 : Vec3)‖ * ‖(Pi.single j 1 : Vec3)‖ *
          ‖(Pi.single j 1 : Vec3)‖ ≤ ‖iteratedFDeriv ℝ 3 X y₀‖ * 1 * 1 * 1 := by
          gcongr <;> exact norm_single_le _
      _ = _ := by ring
  calc ∑ j : Fin 3, |_| ≤ ∑ _j : Fin 3, ‖iteratedFDeriv ℝ 3 X y₀‖ := Finset.sum_le_sum fun j _ => hj j
    _ = 3 * ‖iteratedFDeriv ℝ 3 X y₀‖ := by simp

theorem frob_le {A : Mat3} {m : ℝ} (hm : 0 ≤ m) (h : ∀ i j, |A i j| ≤ m) : frob A ≤ 3 * m := by
  unfold frob
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  calc ∑ i, ∑ j, A i j ^ 2 ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, m ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h i j) 2
    _ = (3 * m) ^ 2 := by simp; ring

end StreamThird

/-- **Lemma 2 (stream cutoff, third derivative)** (source 4917-4937, 5449-5458). -/
theorem streamCutThird (χy : ℝ → ℝ) : UnforcedLeray.Short.PartIIIb.Concrete.StreamCutThird χy := by
  obtain ⟨C4, hC4⟩ := scXJet_of_parts χy scPsiSmooth scPsiBound (scChiJet χy)
  refine ⟨9 * |C4|, ?_⟩
  intro ν B hν hB Z hZ hb hχ s hs
  have hs0 : 0 < s := hs.1
  have hZH : SCZHyp ν B Z := ⟨hZ, hb⟩
  have ht : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
  have hr : cylR (JetClockCore.gam 1 s) = (Real.sqrt s)⁻¹ := by
    have : cylR (JetClockCore.gam 1 s) = Real.sqrt (((Real.sqrt s)⁻¹) ^ 2) := by
      unfold cylR JetClockCore.gam; simp
    rw [this, Real.sqrt_sq (inv_nonneg.2 ht.le)]
  have hrpos : 0 < cylR (JetClockCore.gam 1 s) := by rw [hr]; exact inv_pos.2 ht
  obtain ⟨hcd, hbd⟩ := hC4 ν B hν hB Z hZH hχ _ hrpos
  have h3 := hbd 3 (by norm_num)
  have hcd3 : ContDiffAt ℝ 3 (streamCut ν 1 χy Z) (JetClockCore.gam 1 s) :=
    hcd.of_le (by norm_num)
  have hpow : cylR (JetClockCore.gam 1 s) ^ (-(4 : ℝ) - (3 : ℕ)) = s ^ (7 / 2 : ℝ) := by
    rw [hr, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le, Real.sqrt_eq_rpow,
      ← Real.rpow_mul hs0.le]
    congr 1; push_cast; norm_num
  have hent := fun i k => StreamThird.entry_le hcd3 i k
  have hm : 0 ≤ 3 * ‖iteratedFDeriv ℝ 3 (streamCut ν 1 χy Z) (JetClockCore.gam 1 s)‖ := by positivity
  have hf := StreamThird.frob_le hm (A := fun i j => fderiv ℝ (vecLap (streamCut ν 1 χy Z))
    (JetClockCore.gam 1 s) (Pi.single j 1) i) (fun i j => hent i j)
  rw [hpow] at h3
  calc _ ≤ 3 * (3 * ‖iteratedFDeriv ℝ 3 (streamCut ν 1 χy Z) (JetClockCore.gam 1 s)‖) := hf
    _ ≤ 3 * (3 * (C4 * B * s ^ (7 / 2 : ℝ))) := by gcongr
    _ ≤ 9 * |C4| * B * s ^ (7 / 2 : ℝ) := by
        have : 0 ≤ B * s ^ (7 / 2 : ℝ) := mul_nonneg hB (Real.rpow_nonneg hs0.le _)
        nlinarith [le_abs_self C4]

end UnforcedLeray.Short.PartIIIb.Concrete
