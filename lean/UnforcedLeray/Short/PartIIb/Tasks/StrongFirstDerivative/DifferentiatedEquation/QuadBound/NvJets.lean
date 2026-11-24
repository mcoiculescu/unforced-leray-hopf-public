import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_6_1.L2.Main

/-!
# Second Cartesian derivatives of the ring lift with explicit `R`-dependence
(helper for `PartII-b:S1/1/2`, `DiffEqQuadBound`)

Source `the November 2 reference manuscript`, lines
2346-2366, 2385-2387, 2528-2531.  `nv_jets` (Part III-b) bounds `‖D²N_v b‖ ≤ K Cm ϱ⁻³ W²` with a
constant `K` depending on `R` in an unspecified way.  The same proof, with the constants of the age,
phase and transverse jets kept explicit (`ageJets`, `phaseJets`, `transJets`, `varrho_inv_jet`,
`frameL_jet`, all `R`-independent), gives `K = K₀ (1+R)² R` with `K₀` independent of `R`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb.QuadBoundSub

open UnforcedLeray
open UnforcedLeray.Short.PartIIIb.Concrete (age_eq_sq sqrt_age_eq frame_jet arith_jets clm_apply_le
  smul_le)

/-- Jets of the amplitude `√(age R ·) = R ϱ⁻¹`, constant independent of `R`. -/
theorem amp_jetQ (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (y : Space), 0 < R → y ∉ Axi.axis →
    ‖iteratedFDeriv ℝ n (fun z : Space => √(Axi.age R z)) y‖ ≤
      C * R * ((Axi.ϱ y)⁻¹) ^ (n + 1) := by
  obtain ⟨C, hC, h⟩ := SqrtFrameJetsAux.varrho_inv_jet n
  refine ⟨C, hC, fun R y hR hy => ?_⟩
  have hopen : IsOpen (Axi.axisᶜ : Set Space) := Axi.isOpen_compl_axis
  have hg : ContDiffOn ℝ ∞ (fun w : Space => (Axi.ϱ w)⁻¹) Axi.axisᶜ :=
    Axi.contDiffOn_ϱ.inv fun _ hw => Axi.ϱ_ne_zero hw
  have hdiff : ContDiffAt ℝ n (fun w : Space => (Axi.ϱ w)⁻¹) y :=
    ((hg.contDiffAt (hopen.mem_nhds hy)).of_le (by exact_mod_cast le_top))
  rw [sqrt_age_eq hR, show (fun z : Space => R * (Axi.ϱ z)⁻¹) = R • (fun z : Space => (Axi.ϱ z)⁻¹)
    from rfl, iteratedFDeriv_const_smul_apply hdiff, norm_smul, Real.norm_of_nonneg hR.le]
  calc R * ‖iteratedFDeriv ℝ n (fun z : Space => (Axi.ϱ z)⁻¹) y‖ ≤ R * (C * ((Axi.ϱ y)⁻¹) ^ (n + 1)) :=
        mul_le_mul_of_nonneg_left (h y hy) hR.le
    _ = C * R * ((Axi.ϱ y)⁻¹) ^ (n + 1) := by ring

/-- Jets of the chart `(s, ξ, η)`, order `n ≥ 1`: `≲ (1+R) t^n (1 + s + |η|)`, constant
independent of `R`. -/
theorem chart_jetQ (n : ℕ) (hn : 1 ≤ n) : ∃ a : ℝ, 0 < a ∧
    ∀ (R τ : ℝ) (y : Space), 0 < R → y ∉ Axi.axis →
      ‖iteratedFDeriv ℝ n (Axi.chart R τ) y‖ ≤
        a * (1 + R) * ((Axi.ϱ y)⁻¹) ^ n * (1 + Axi.age R y + |Axi.trans R y|) := by
  obtain ⟨CA, hCA, hA'⟩ := ageJets n
  obtain ⟨CP, hCP, hP'⟩ := phaseJets n hn
  obtain ⟨CT, hCT, hT'⟩ := transJets n hn
  refine ⟨CA + CP + CT, by positivity, ?_⟩
  intro R τ y hR hy
  have hU : Axi.axisᶜ ∈ 𝓝 y := Axi.isOpen_compl_axis.mem_nhds hy
  have cA : ContDiffAt ℝ ∞ (Axi.age R) y := (ChartJetsAux.contDiffOn_age R).contDiffAt hU
  have cP : ContDiffAt ℝ ∞ (Axi.phase R τ) y :=
    (ChartJetsAux.contDiffOn_phase hR.ne' τ).contDiffAt hU
  have cT : ContDiffAt ℝ ∞ (Axi.trans R) y := (ChartJetsAux.contDiffOn_trans R).contDiffAt hU
  have hn' : ((n : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hD : iteratedFDeriv ℝ n (Axi.chart R τ) y =
      (iteratedFDeriv ℝ n (Axi.age R) y).prod
        ((iteratedFDeriv ℝ n (Axi.phase R τ) y).prod (iteratedFDeriv ℝ n (Axi.trans R) y)) := by
    rw [show Axi.chart R τ = fun x => (Axi.age R x, (Axi.phase R τ x, Axi.trans R x)) from rfl,
      iteratedFDeriv_prodMk cA (cP.prodMk cT) hn', iteratedFDeriv_prodMk cP cT hn']
  rw [hD, ContinuousMultilinearMap.opNorm_prod, ContinuousMultilinearMap.opNorm_prod]
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (Axi.ϱ y)⁻¹ := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; exact inv_nonneg.2 (Axi.ϱ_nonneg y)
  have hs : Axi.age R y = R ^ 2 * t ^ 2 := by rw [age_eq_sq, ht]
  have hη0 : 0 ≤ |Axi.trans R y| := abs_nonneg _
  have hs0 : 0 ≤ Axi.age R y := by rw [hs]; positivity
  set W : ℝ := 1 + Axi.age R y + |Axi.trans R y| with hW
  have hW1 : 1 ≤ W := by rw [hW]; linarith
  rw [← ht]
  have tn : 0 ≤ t ^ n := pow_nonneg ht0 n
  have hTW : 0 ≤ t ^ n * W := by positivity
  have bA : ‖iteratedFDeriv ℝ n (Axi.age R) y‖ ≤ CA * t ^ n * W := by
    have h := hA' R y hy
    rw [← ht] at h
    have e : CA * R ^ 2 * t ^ (n + 2) = CA * t ^ n * Axi.age R y := by rw [hs]; ring
    rw [e] at h
    refine h.trans ?_
    have : Axi.age R y ≤ W := by rw [hW]; linarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have bP : ‖iteratedFDeriv ℝ n (Axi.phase R τ) y‖ ≤ CP * R * t ^ n * W := by
    have h := hP' R τ y hR hy
    rw [← ht] at h
    refine h.trans ?_
    have : CP * R * t ^ n * 1 ≤ CP * R * t ^ n * W :=
      mul_le_mul_of_nonneg_left hW1 (by positivity)
    linarith
  have bT : ‖iteratedFDeriv ℝ n (Axi.trans R) y‖ ≤ CT * (1 + R) * t ^ n * W := by
    have h := hT' R y hR hy
    rw [← ht] at h
    refine h.trans ?_
    have h1 : |Axi.trans R y| + R ≤ (1 + R) * W := by rw [hW]; nlinarith
    calc CT * (|Axi.trans R y| + R) * t ^ n = CT * t ^ n * (|Axi.trans R y| + R) := by ring
      _ ≤ CT * t ^ n * ((1 + R) * W) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = CT * (1 + R) * t ^ n * W := by ring
  have e1 : (CA + CP + CT) * (1 + R) * t ^ n * W =
      CA * (1 + R) * (t ^ n * W) + CP * (1 + R) * (t ^ n * W) + CT * (1 + R) * t ^ n * W := by
    ring
  have p1 : CA * t ^ n * W ≤ CA * (1 + R) * (t ^ n * W) := by
    have : CA * (t ^ n * W) ≤ CA * (1 + R) * (t ^ n * W) := by
      have := mul_le_mul_of_nonneg_right (show CA ≤ CA * (1 + R) by nlinarith) hTW
      linarith
    linarith [show CA * t ^ n * W = CA * (t ^ n * W) by ring]
  have p2 : CP * R * t ^ n * W ≤ CP * (1 + R) * (t ^ n * W) := by
    have := mul_le_mul_of_nonneg_right (show CP * R ≤ CP * (1 + R) by nlinarith) hTW
    linarith [show CP * R * t ^ n * W = CP * R * (t ^ n * W) by ring]
  have q1 : 0 ≤ CA * (1 + R) * (t ^ n * W) := by positivity
  have q2 : 0 ≤ CP * (1 + R) * (t ^ n * W) := by positivity
  have q3 : 0 ≤ CT * (1 + R) * t ^ n * W := by positivity
  refine max_le ?_ (max_le ?_ ?_)
  · rw [e1]; linarith
  · rw [e1]; linarith
  · rw [e1]; linarith

/-- Faà di Bruno for `b ∘ chart`, orders `1, 2`, with the chart constant `a₀ (1+R)`. -/
theorem comp_jetQ : ∃ a0 : ℝ, 1 ≤ a0 ∧ ∀ (R τ : ℝ) (b : ℝ × (ℝ × ℝ) → Axi.Merid), 0 < R →
    ContDiff ℝ ∞ b → ∀ (y : Space), y ∉ Axi.axis → ∀ Cm : ℝ,
    (∀ i ≤ 2, ‖iteratedFDeriv ℝ i b (Axi.chart R τ y)‖ ≤ Cm) → ∀ n : ℕ, 1 ≤ n → n ≤ 2 →
      ‖iteratedFDeriv ℝ n (fun z => b (Axi.chart R τ z)) y‖ ≤
        (n.factorial : ℝ) * Cm *
          (a0 * (1 + R) * (Axi.ϱ y)⁻¹ * (1 + Axi.age R y + |Axi.trans R y|)) ^ n := by
  obtain ⟨a1, ha1, h1⟩ := chart_jetQ 1 le_rfl
  obtain ⟨a2, ha2, h2⟩ := chart_jetQ 2 (by norm_num)
  refine ⟨1 + a1 + a2, by linarith, ?_⟩
  intro R τ b hR hb y hy Cm hCm n hn1 hn2
  have hopen : IsOpen (Axi.axisᶜ : Set Space) := Axi.isOpen_compl_axis
  have hx : y ∈ (Axi.axisᶜ : Set Space) := hy
  have hchart : ContDiffOn ℝ ∞ (Axi.chart R τ) Axi.axisᶜ :=
    ChartJetsAux.contDiffOn_chart hR.ne' τ
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (Axi.ϱ y)⁻¹ := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; exact inv_nonneg.2 (Axi.ϱ_nonneg y)
  have hs : Axi.age R y = R ^ 2 * t ^ 2 := by rw [age_eq_sq, ht]
  have hs0 : 0 ≤ Axi.age R y := by rw [hs]; positivity
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = 1 + Axi.age R y + |Axi.trans R y| := ⟨_, rfl⟩
  have hW1 : 1 ≤ W := by rw [hW]; linarith [abs_nonneg (Axi.trans R y)]
  set a : ℝ := (1 + a1 + a2) * (1 + R) with ha
  have ha1' : 1 ≤ a := by
    rw [ha]; nlinarith
  rw [← ht, ← hW]
  have hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDerivWithin ℝ i (Axi.chart R τ) Axi.axisᶜ y‖
      ≤ (a * t * W) ^ i := by
    intro i hi1 hin
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) i hopen hx]
    have hi2 : i ≤ 2 := hin.trans hn2
    have hb1 : ‖iteratedFDeriv ℝ i (Axi.chart R τ) y‖ ≤ a * t ^ i * W := by
      have hle : ∀ ai : ℝ, ai ≤ 1 + a1 + a2 →
          ‖iteratedFDeriv ℝ i (Axi.chart R τ) y‖ ≤ ai * (1 + R) * t ^ i * W →
          ‖iteratedFDeriv ℝ i (Axi.chart R τ) y‖ ≤ a * t ^ i * W := by
        intro ai hai h
        refine h.trans ?_
        rw [ha]
        have hR1 : 0 ≤ 1 + R := by linarith
        have : ai * (1 + R) ≤ (1 + a1 + a2) * (1 + R) := mul_le_mul_of_nonneg_right hai hR1
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this (pow_nonneg ht0 i))
          (by linarith)
      interval_cases i
      · refine hle a1 (by linarith) ?_
        have := h1 R τ y hR hy
        rw [← ht, ← hW] at this
        simpa using this
      · refine hle a2 (by linarith) ?_
        have := h2 R τ y hR hy
        rw [← ht, ← hW] at this
        simpa using this
    refine hb1.trans ?_
    calc a * t ^ i * W ≤ a ^ i * t ^ i * W ^ i := by
          refine mul_le_mul (mul_le_mul (le_self_pow₀ ha1' (by omega)) le_rfl (pow_nonneg ht0 i)
            (by positivity)) (le_self_pow₀ hW1 (by omega)) (by linarith) (by positivity)
      _ = (a * t * W) ^ i := by ring
  have hbound0 : ∀ i, i ≤ n → ‖iteratedFDerivWithin ℝ i b univ (Axi.chart R τ y)‖ ≤ Cm := by
    intro i hi
    rw [iteratedFDerivWithin_univ]
    exact hCm i (hi.trans hn2)
  have key := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (g := b) (f := Axi.chart R τ)
    (n := n) (s := Axi.axisᶜ) (t := univ) (x := y) (N := ∞)
    hb.contDiffOn hchart (by exact_mod_cast le_top) uniqueDiffOn_univ hopen.uniqueDiffOn
    (mapsTo_univ _ _) hx hbound0 hD
  have e : iteratedFDeriv ℝ n (fun z => b (Axi.chart R τ z)) y =
      iteratedFDerivWithin ℝ n (b ∘ Axi.chart R τ) Axi.axisᶜ y :=
    (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) n hopen hx).symm
  rw [e]
  exact key

/-- **Second derivatives of the ring lift**, explicit in `R`:
`‖D²N_v b‖ ≤ K (1+R)² R Cm ϱ⁻³ (1+s+|η|)²` with `K` independent of `R`. -/
theorem nv_jetsQ : ∃ K : ℝ, 0 < K ∧
    ∀ (R τ : ℝ) (b : ℝ × (ℝ × ℝ) → Axi.Merid), 0 < R → ContDiff ℝ ∞ b →
    ∀ y : Space, y ∉ Axi.axis →
    ∀ Cm : ℝ, (∀ i ≤ 2, ‖iteratedFDeriv ℝ i b (Axi.chart R τ y)‖ ≤ Cm) →
      ‖iteratedFDeriv ℝ 2 (Axi.Nv R b τ) y‖ ≤
        K * (1 + R) ^ 2 * R * Cm * ((Axi.ϱ y)⁻¹) ^ 3 *
          (1 + Axi.age R y + |Axi.trans R y|) ^ 2 := by
  obtain ⟨α0, hα0, hA0⟩ := amp_jetQ 0
  obtain ⟨α1, hα1, hA1⟩ := amp_jetQ 1
  obtain ⟨α2, hα2, hA2⟩ := amp_jetQ 2
  obtain ⟨π0, hπ0, hP0⟩ := frame_jet 0
  obtain ⟨π1, hπ1, hP1⟩ := frame_jet 1
  obtain ⟨π2, hπ2, hP2⟩ := frame_jet 2
  obtain ⟨a0, ha0, hcomp⟩ := comp_jetQ
  refine ⟨10 * (α0 + α1 + α2) * (π0 + π1 + π2) * a0 ^ 2, by positivity, ?_⟩
  intro R τ b hR hb y hy Cm hCm
  have hopen : IsOpen (Axi.axisᶜ : Set Space) := Axi.isOpen_compl_axis
  have hx : y ∈ (Axi.axisᶜ : Set Space) := hy
  have hCm0 : 0 ≤ Cm := (norm_nonneg _).trans (hCm 0 (by norm_num))
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (Axi.ϱ y)⁻¹ := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; exact inv_nonneg.2 (Axi.ϱ_nonneg y)
  have hs : Axi.age R y = R ^ 2 * t ^ 2 := by rw [age_eq_sq, ht]
  have hs0 : 0 ≤ Axi.age R y := by rw [hs]; positivity
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = 1 + Axi.age R y + |Axi.trans R y| := ⟨_, rfl⟩
  have hW1 : 1 ≤ W := by rw [hW]; linarith [abs_nonneg (Axi.trans R y)]
  set a : ℝ := a0 * (1 + R) with ha
  have ha1 : 1 ≤ a := by rw [ha]; nlinarith
  rw [← ht, ← hW]
  have hAc : ContDiffOn ℝ ∞ (fun z : Space => √(Axi.age R z)) Axi.axisᶜ :=
    ChartJetsAux.contDiffOn_sqrt_age hR.ne'
  have hPc : ContDiffOn ℝ ∞ Axi.frameL Axi.axisᶜ := ChartJetsAux.contDiffOn_frameL
  have hBc : ContDiffOn ℝ ∞ (fun z : Space => b (Axi.chart R τ z)) Axi.axisᶜ :=
    ChartJetsAux.contDiffOn_comp_chart hb hR.ne' τ
  obtain ⟨hG0, hG1, hG2⟩ := clm_apply_le hopen hx hPc hBc
  have hGc : ContDiffOn ℝ ∞ (fun z : Space => Axi.frameL z (b (Axi.chart R τ z))) Axi.axisᶜ :=
    hPc.clm_apply hBc
  obtain ⟨hN1, hN2⟩ := smul_le hopen hx hAc hGc
  have hNv : Axi.Nv R b τ = fun z => √(Axi.age R z) • Axi.frameL z (b (Axi.chart R τ z)) := rfl
  rw [hNv]
  have bA0 := hA0 R y hR hy
  have bA1 := hA1 R y hR hy
  have bA2 := hA2 R y hR hy
  have bP0 := hP0 y hy
  have bP1 := hP1 y hy
  have bP2 := hP2 y hy
  rw [← ht] at bA0 bA1 bA2 bP0 bP1 bP2
  simp only [zero_add, pow_zero, mul_one, Nat.reduceAdd, pow_one] at bA0 bA1 bA2 bP0 bP1 bP2
  have bB0 : ‖iteratedFDeriv ℝ 0 (fun z => b (Axi.chart R τ z)) y‖ ≤ Cm := by
    rw [norm_iteratedFDeriv_zero]
    simpa using hCm 0 (by norm_num)
  have bB1 := hcomp R τ b hR hb y hy Cm hCm 1 le_rfl (by norm_num)
  have bB2 := hcomp R τ b hR hb y hy Cm hCm 2 (by norm_num) le_rfl
  rw [← ht, ← hW, ← ha] at bB1 bB2
  have hαs : 0 ≤ α0 + α1 + α2 := by positivity
  have hπs : 0 ≤ π0 + π1 + π2 := by positivity
  have key := arith_jets (α0 + α1 + α2) (π0 + π1 + π2) a R Cm t W _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hαs hπs ha1 hR hCm0 ht0 hW1 (bA0.trans (by gcongr; linarith))
    (bA1.trans (by gcongr; linarith)) (bA2.trans (by gcongr; linarith))
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (bP0.trans (by linarith))
    (bP1.trans (by gcongr; linarith)) (bP2.trans (by gcongr; linarith))
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) bB0
    (by simp only [Nat.factorial_one, Nat.cast_one, one_mul, pow_one] at bB1; exact bB1)
    (by simp only [Nat.factorial_two, Nat.cast_ofNat] at bB2; exact bB2)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hG0 hG1 hG2 (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) hN1 hN2
  refine key.2.trans (le_of_eq ?_)
  rw [ha]
  ring

end UnforcedLeray.Short.IIb.QuadBoundSub
