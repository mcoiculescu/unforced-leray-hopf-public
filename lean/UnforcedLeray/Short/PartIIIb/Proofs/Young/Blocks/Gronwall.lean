import UnforcedLeray.Short.PartIIIb.Concrete.YoungBlocks
import UnforcedLeray.Short.PartIIIb.Proofs.Young.Blocks.Gronwall.Kernel

/-!
# The block Gronwall step (source 4396-4406)

Proves `ConcreteYF.BlockGronwall`, the real-analysis Gronwall step of the retained block
estimates (`YoungBlocks.lean`).  Writing `X = |α_+| + |α_-|`, `S = X(t) + ρ(t)`:

* `psi_bound`: `g ∫_t^s ρ ≤ Cρ(t) + Ck ∫_t^s X` (from the kernel identity of `Kernel.lean`);
* `block_core`: the integral Gronwall inequality for `X` (via `gronwall_int`), giving
  `X(s) ≤ K₁ S` with `K₁` depending only on `C, g, B`.

The three conclusions of `BlockGronwall` then follow with `K = K₁ + K₂ + K₃`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb

open BlockGronwallAux

/-! ## Constants -/

/-- `D = 2CB + 2C²B/g`: bound for `c (s - t)` with `c = 2Cε + 2C²k²/g`. -/
def blockD (C g B : ℝ) : ℝ := 2 * C * B + 2 * C ^ 2 * B / g

/-- `K₁ = (1 + 2C²B/g)(1 + D e^D)`: bound of `X` by `K₁ (X(t) + ρ(t))`. -/
def blockK1 (C g B : ℝ) : ℝ :=
  (1 + 2 * C ^ 2 * B / g) * (1 + blockD C g B * Real.exp (blockD C g B))

/-- `K₂`: bound of the increments of `α_j`. -/
def blockK2 (C g B : ℝ) : ℝ := C * blockK1 C g B + C ^ 2 / g + C ^ 2 * blockK1 C g B / g

/-- `K₃`: bound of the complement. -/
def blockK3 (C g B : ℝ) : ℝ := C + C * blockK1 C g B / g

theorem blockD_nonneg {C g B : ℝ} (hC : 0 < C) (hg : 0 < g) (hB : 0 < B) :
    0 ≤ blockD C g B := by
  unfold blockD
  exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC.le) hB.le)
    (div_nonneg (mul_nonneg (by positivity) hB.le) hg.le)

theorem blockK1_nonneg {C g B : ℝ} (hC : 0 < C) (hg : 0 < g) (hB : 0 < B) :
    0 ≤ blockK1 C g B := by
  unfold blockK1
  exact mul_nonneg (add_nonneg zero_le_one (div_nonneg (mul_nonneg (by positivity) hB.le) hg.le))
    (add_nonneg zero_le_one (mul_nonneg (blockD_nonneg hC hg hB) (Real.exp_pos _).le))

/-! ## The complement integral -/

/-- `g ∫_t^s ρ ≤ Cρ(t) + Ck ∫_t^s X` under the complement estimate. -/
theorem psi_bound {C g k t T : ℝ} {X ρ : ℝ → ℝ} (hC : 0 ≤ C) (hk : 0 ≤ k) (hg : 0 < g)
    (hT : t ≤ T) (hX : ContinuousOn X (Icc t T)) (hX0 : ∀ r ∈ Icc t T, 0 ≤ X r)
    (hρ0 : ∀ r, 0 ≤ ρ r) (hρc : ContinuousOn ρ (Icc t T))
    (hR : ∀ s ∈ Icc t T, ρ s ≤ C * Real.exp (-g * (s - t)) * ρ t +
      C * k * ∫ r in t..s, Real.exp (-g * (s - r)) * X r)
    {s : ℝ} (hs : s ∈ Icc t T) :
    g * ∫ u in t..s, ρ u ≤ C * ρ t + C * k * ∫ r in t..s, X r := by
  have hts : t ≤ s := hs.1
  have hsub : Icc t s ⊆ Icc t T := Icc_subset_Icc le_rfl hs.2
  have hXs : ContinuousOn X (Icc t s) := hX.mono hsub
  have hρs : ContinuousOn ρ (Icc t s) := hρc.mono hsub
  have hEc : ContinuousOn (fun u => C * Real.exp (-g * (u - t)) * ρ t) (Icc t s) :=
    (by fun_prop : Continuous (fun u : ℝ => C * Real.exp (-g * (u - t)) * ρ t)).continuousOn
  have hKc := kernel_continuousOn (g := g) hts hXs
  have hEi : IntervalIntegrable (fun u => C * Real.exp (-g * (u - t)) * ρ t) volume t s :=
    ContinuousOn.intervalIntegrable (by rw [Set.uIcc_of_le hts]; exact hEc)
  have hKi : IntervalIntegrable
      (fun u => C * k * ∫ r in t..u, Real.exp (-g * (u - r)) * X r) volume t s :=
    ContinuousOn.intervalIntegrable (by rw [Set.uIcc_of_le hts]; exact continuousOn_const.mul hKc)
  have hρi : IntervalIntegrable ρ volume t s :=
    ContinuousOn.intervalIntegrable (by rw [Set.uIcc_of_le hts]; exact hρs)
  have hmono : (∫ u in t..s, ρ u) ≤ ∫ u in t..s, (C * Real.exp (-g * (u - t)) * ρ t +
      C * k * ∫ r in t..u, Real.exp (-g * (u - r)) * X r) :=
    intervalIntegral.integral_mono_on hts hρi (hEi.add hKi)
      (fun u hu => hR u ⟨hu.1, hu.2.trans hs.2⟩)
  rw [intervalIntegral.integral_add hEi hKi] at hmono
  have e1 : (∫ u in t..s, C * Real.exp (-g * (u - t)) * ρ t) =
      (C * ρ t) * ∫ u in t..s, Real.exp (-g * (u - t)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only
    ring
  rw [e1, intervalIntegral.integral_const_mul (C * k)] at hmono
  have hEx : g * ∫ u in t..s, Real.exp (-g * (u - t)) ≤ 1 := by
    have h := integral_exp_neg_start_le hg hts
    calc g * ∫ u in t..s, Real.exp (-g * (u - t)) ≤ g * (1 / g) :=
          mul_le_mul_of_nonneg_left h hg.le
      _ = 1 := mul_one_div_cancel hg.ne'
  have hJid := kernel_integral_identity (g := g) hT hX hs
  have hJnn := kernel_nonneg (g := g) (X := X) hts (fun r hr => hX0 r ⟨hr.1, hr.2.trans hs.2⟩)
  have hJ2 : g * ∫ u in t..s, (∫ r in t..u, Real.exp (-g * (u - r)) * X r) ≤
      ∫ r in t..s, X r := by
    linarith
  have hρt : 0 ≤ ρ t := hρ0 t
  have h3 := mul_le_mul_of_nonneg_left hmono hg.le
  have h4 : C * ρ t * (g * ∫ u in t..s, Real.exp (-g * (u - t))) ≤ C * ρ t * 1 :=
    mul_le_mul_of_nonneg_left hEx (mul_nonneg hC hρt)
  have h5 : C * k * (g * ∫ u in t..s, (∫ r in t..u, Real.exp (-g * (u - r)) * X r)) ≤
      C * k * ∫ r in t..s, X r :=
    mul_le_mul_of_nonneg_left hJ2 (mul_nonneg hC hk)
  nlinarith [h3, h4, h5]

/-! ## The Gronwall core for `X = |α_+| + |α_-|` -/

theorem block_core {C g B ε k L t : ℝ} {X ρ : ℝ → ℝ} (hC : 0 < C) (hg : 0 < g) (hB : 0 < B)
    (hε : 0 ≤ ε) (hk : 0 ≤ k) (hL : 0 ≤ L) (hεL : ε * L ≤ B) (hkB : k ≤ B)
    (hk2L : k ^ 2 * L ≤ B)
    (hX0 : ∀ r ∈ Icc t (t + L), 0 ≤ X r) (hρ0 : ∀ r, 0 ≤ ρ r)
    (hXc : ContinuousOn X (Icc t (t + L))) (hρc : ContinuousOn ρ (Icc t (t + L)))
    (hR : ∀ s ∈ Icc t (t + L), ρ s ≤ C * Real.exp (-g * (s - t)) * ρ t +
      C * k * ∫ r in t..s, Real.exp (-g * (s - r)) * X r)
    (hA : ∀ s ∈ Icc t (t + L), X s ≤ X t + 2 * ∫ r in t..s, (C * ε * X r + C * k * ρ r)) :
    ∀ s ∈ Icc t (t + L), X s ≤ blockK1 C g B * (X t + ρ t) := by
  intro s hs
  have hg0 : 0 ≤ g := hg.le
  have hT : t ≤ t + L := by linarith
  have hXt : 0 ≤ X t := hX0 t ⟨le_rfl, by linarith⟩
  have hρt : 0 ≤ ρ t := hρ0 t
  have hCk : 0 ≤ C := hC.le
  -- the integral inequality for `X` with the Gronwall constants
  have hb : ∀ u ∈ Icc t (t + L), X u ≤ (X t + 2 * C ^ 2 * k * ρ t / g) +
      (2 * C * ε + 2 * C ^ 2 * k ^ 2 / g) * ∫ r in t..u, X r := by
    intro u hu
    have hXi : IntervalIntegrable X volume t u := intervalIntegrable_of_cont hXc hu
    have hρi : IntervalIntegrable ρ volume t u := intervalIntegrable_of_cont hρc hu
    have hsplit : (∫ r in t..u, (C * ε * X r + C * k * ρ r)) =
        C * ε * (∫ r in t..u, X r) + C * k * (∫ r in t..u, ρ r) := by
      rw [intervalIntegral.integral_add (hXi.const_mul (C * ε)) (hρi.const_mul (C * k)),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hpsi := psi_bound hCk hk hg hT hXc hX0 hρ0 hρc hR hu
    have hpsi' : ∫ r in t..u, ρ r ≤ (C * ρ t + C * k * ∫ r in t..u, X r) / g := by
      rw [le_div_iff₀ hg]
      linarith
    have hpsi2 : 2 * C * k * ∫ r in t..u, ρ r ≤
        2 * C ^ 2 * k * ρ t / g + 2 * C ^ 2 * k ^ 2 / g * ∫ r in t..u, X r := by
      have h := mul_le_mul_of_nonneg_left hpsi'
        (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hCk) hk)
      have e2 : 2 * C * k * ((C * ρ t + C * k * ∫ r in t..u, X r) / g) =
          2 * C ^ 2 * k * ρ t / g + 2 * C ^ 2 * k ^ 2 / g * ∫ r in t..u, X r := by
        ring
      linarith
    have h1 := hA u hu
    linarith [h1, hsplit, hpsi2]
  have hA0 : 0 ≤ X t + 2 * C ^ 2 * k * ρ t / g :=
    add_nonneg hXt (div_nonneg (mul_nonneg (mul_nonneg (by positivity) hk) hρt) hg0)
  have hc0 : 0 ≤ 2 * C * ε + 2 * C ^ 2 * k ^ 2 / g :=
    add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCk) hε)
      (div_nonneg (mul_nonneg (by positivity) (sq_nonneg k)) hg0)
  have hG1 := gronwall_int hXc hA0 hc0 hb s hs
  have hst0 : 0 ≤ s - t := by linarith [hs.1]
  have hst : s - t ≤ L := by linarith [hs.2]
  have hD0 := blockD_nonneg hC hg hB
  have hu_le : (2 * C * ε + 2 * C ^ 2 * k ^ 2 / g) * (s - t) ≤ blockD C g B := by
    have h1 : ε * (s - t) ≤ B := le_trans (mul_le_mul_of_nonneg_left hst hε) hεL
    have h2 : k ^ 2 * (s - t) ≤ B := le_trans (mul_le_mul_of_nonneg_left hst (sq_nonneg k)) hk2L
    have h3 : 2 * C * (ε * (s - t)) ≤ 2 * C * B :=
      mul_le_mul_of_nonneg_left h1 (mul_nonneg (by norm_num) hCk)
    have h4 : 2 * C ^ 2 / g * (k ^ 2 * (s - t)) ≤ 2 * C ^ 2 / g * B :=
      mul_le_mul_of_nonneg_left h2 (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg C)) hg0)
    have e : (2 * C * ε + 2 * C ^ 2 * k ^ 2 / g) * (s - t) =
        2 * C * (ε * (s - t)) + 2 * C ^ 2 / g * (k ^ 2 * (s - t)) := by ring
    have e2 : 2 * C ^ 2 / g * B = 2 * C ^ 2 * B / g := by ring
    unfold blockD
    rw [e]
    linarith
  have hexp : Real.exp ((2 * C * ε + 2 * C ^ 2 * k ^ 2 / g) * (s - t)) ≤
      Real.exp (blockD C g B) :=
    Real.exp_le_exp.2 hu_le
  have hue : (2 * C * ε + 2 * C ^ 2 * k ^ 2 / g) * (s - t) *
      Real.exp ((2 * C * ε + 2 * C ^ 2 * k ^ 2 / g) * (s - t)) ≤
      blockD C g B * Real.exp (blockD C g B) :=
    mul_le_mul hu_le hexp (Real.exp_pos _).le hD0
  have hbound : X s ≤ (X t + 2 * C ^ 2 * k * ρ t / g) *
      (1 + blockD C g B * Real.exp (blockD C g B)) := by
    have e3 : (2 * C * ε + 2 * C ^ 2 * k ^ 2 / g) *
        ((X t + 2 * C ^ 2 * k * ρ t / g) * (s - t) *
          Real.exp ((2 * C * ε + 2 * C ^ 2 * k ^ 2 / g) * (s - t))) =
        (X t + 2 * C ^ 2 * k * ρ t / g) *
          ((2 * C * ε + 2 * C ^ 2 * k ^ 2 / g) * (s - t) *
            Real.exp ((2 * C * ε + 2 * C ^ 2 * k ^ 2 / g) * (s - t))) := by
      ring
    have h5 := mul_le_mul_of_nonneg_left hue hA0
    have hG2 := hG1
    linarith [hG2, e3, h5]
  have hkA : 2 * C ^ 2 * k / g ≤ 2 * C ^ 2 * B / g := by
    gcongr
  have hA_le : X t + 2 * C ^ 2 * k * ρ t / g ≤ (1 + 2 * C ^ 2 * B / g) * (X t + ρ t) := by
    have e : 2 * C ^ 2 * k * ρ t / g = (2 * C ^ 2 * k / g) * ρ t := by ring
    have h6 : (2 * C ^ 2 * k / g) * ρ t ≤ (2 * C ^ 2 * B / g) * ρ t :=
      mul_le_mul_of_nonneg_right hkA hρt
    have h7 : 0 ≤ (2 * C ^ 2 * B / g) * X t :=
      mul_nonneg (div_nonneg (mul_nonneg (by positivity) hB.le) hg0) hXt
    rw [e]
    nlinarith [h6, h7]
  have hc1 : 0 ≤ 1 + blockD C g B * Real.exp (blockD C g B) := by
    have := mul_nonneg hD0 (Real.exp_pos (blockD C g B)).le
    linarith
  have hfin : (X t + 2 * C ^ 2 * k * ρ t / g) * (1 + blockD C g B * Real.exp (blockD C g B)) ≤
      (1 + 2 * C ^ 2 * B / g) * (X t + ρ t) *
        (1 + blockD C g B * Real.exp (blockD C g B)) :=
    mul_le_mul_of_nonneg_right hA_le hc1
  unfold blockK1
  linarith [hbound, hfin]

/-! ## The block Gronwall step -/

/-- **Target** (source 4396-4406): the Gronwall consequence of the retained block estimates. -/
theorem blockGronwall_holds : ConcreteYF.BlockGronwall := by
  intro C g B hC hg hB
  have hK1 := blockK1_nonneg hC hg hB
  have hK2 : 0 ≤ blockK2 C g B := by
    unfold blockK2
    exact add_nonneg (add_nonneg (mul_nonneg hC.le hK1) (div_nonneg (sq_nonneg C) hg.le))
      (div_nonneg (mul_nonneg (sq_nonneg C) hK1) hg.le)
  have hK3 : 0 ≤ blockK3 C g B := by
    unfold blockK3
    exact add_nonneg hC.le (div_nonneg (mul_nonneg hC.le hK1) hg.le)
  obtain ⟨K, hK1K, hK2K, hK3K⟩ : ∃ K : ℝ, blockK1 C g B ≤ K ∧ blockK2 C g B ≤ K ∧
      blockK3 C g B ≤ K :=
    ⟨blockK1 C g B + blockK2 C g B + blockK3 C g B, by linarith, by linarith, by linarith⟩
  have hK0 : 0 ≤ K := le_trans hK1 hK1K
  refine ⟨K, hK0, ?_⟩
  intro ε k L t α ρ hε hk hL hεL hkB hk2L hρ0 hαc hρc hR hA
  intro s hs
  have hT : t ≤ t + L := by linarith
  have hXc : ContinuousOn (fun r => ‖α true r‖ + ‖α false r‖) (Icc t (t + L)) :=
    ((hαc true).norm).add ((hαc false).norm)
  have hX0 : ∀ r ∈ Icc t (t + L), 0 ≤ ‖α true r‖ + ‖α false r‖ := fun r _ =>
    add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hA1 : ∀ u ∈ Icc t (t + L), ‖α true u‖ + ‖α false u‖ ≤
      (‖α true t‖ + ‖α false t‖) +
        2 * ∫ r in t..u, (C * ε * (‖α true r‖ + ‖α false r‖) + C * k * ρ r) := by
    intro u hu
    have h1 := hA true u hu
    have h2 := hA false u hu
    have n1 := norm_sub_norm_le (α true u) (α true t)
    have n2 := norm_sub_norm_le (α false u) (α false t)
    linarith
  have hcore := block_core (X := fun r => ‖α true r‖ + ‖α false r‖) (ρ := ρ) hC hg hB hε hk hL
    hεL hkB hk2L hX0 hρ0 hXc hρc hR hA1
  have hS0 : 0 ≤ (‖α true t‖ + ‖α false t‖) + ρ t :=
    add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (hρ0 t)
  have hρt : 0 ≤ ρ t := hρ0 t
  have hXt : 0 ≤ ‖α true t‖ + ‖α false t‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hρS : ρ t ≤ (‖α true t‖ + ‖α false t‖) + ρ t := by linarith
  have hK1S0 : 0 ≤ blockK1 C g B * ((‖α true t‖ + ‖α false t‖) + ρ t) :=
    mul_nonneg hK1 hS0
  -- the pointwise bound of `X` on `[t, s]`
  have hcr : ∀ r ∈ Icc t s, ‖α true r‖ + ‖α false r‖ ≤
      blockK1 C g B * ((‖α true t‖ + ‖α false t‖) + ρ t) := fun r hr =>
    block_core (X := fun r => ‖α true r‖ + ‖α false r‖) (ρ := ρ) hC hg hB hε hk hL hεL hkB hk2L
      hX0 hρ0 hXc hρc hR hA1 r ⟨hr.1, hr.2.trans hs.2⟩
  have hcs : ‖α true s‖ + ‖α false s‖ ≤ blockK1 C g B * ((‖α true t‖ + ‖α false t‖) + ρ t) :=
    hcore s hs
  have hts : t ≤ s := hs.1
  have hsub : Icc t s ⊆ Icc t (t + L) := Icc_subset_Icc le_rfl hs.2
  have hXs : ContinuousOn (fun r => ‖α true r‖ + ‖α false r‖) (Icc t s) := hXc.mono hsub
  have hρs : ContinuousOn ρ (Icc t s) := hρc.mono hsub
  -- part (1)
  have p1 : ‖α true s‖ + ‖α false s‖ ≤ K * ((‖α true t‖ + ‖α false t‖) + ρ t) :=
    le_trans hcs (mul_le_mul_of_nonneg_right hK1K hS0)
  -- the integral of `X` over `[t, s]`
  have hI_le : ∫ r in t..s, (‖α true r‖ + ‖α false r‖) ≤
      L * (blockK1 C g B * ((‖α true t‖ + ‖α false t‖) + ρ t)) := by
    have hm := intervalIntegral.integral_mono_on hts
      (intervalIntegrable_of_cont hXc hs)
      (intervalIntegrable_const (c := blockK1 C g B * ((‖α true t‖ + ‖α false t‖) + ρ t)))
      (fun r hr => hcr r hr)
    rw [intervalIntegral.integral_const, smul_eq_mul] at hm
    have h2 : (s - t) * (blockK1 C g B * ((‖α true t‖ + ‖α false t‖) + ρ t)) ≤
        L * (blockK1 C g B * ((‖α true t‖ + ‖α false t‖) + ρ t)) :=
      mul_le_mul_of_nonneg_right (by linarith [hs.2]) hK1S0
    linarith
  -- the complement integral
  have hP := psi_bound hC.le hk hg hT hXc hX0 hρ0 hρc hR hs
  have hP' : ∫ r in t..s, ρ r ≤ (C * ρ t + C * k * ∫ r in t..s, (‖α true r‖ + ‖α false r‖)) / g := by
    rw [le_div_iff₀ hg]
    linarith
  have hPk : C * k * ∫ r in t..s, ρ r ≤
      C ^ 2 * k * ρ t / g + C ^ 2 * k ^ 2 / g * ∫ r in t..s, (‖α true r‖ + ‖α false r‖) := by
    have h := mul_le_mul_of_nonneg_left hP' (mul_nonneg hC.le hk)
    have e : C * k * ((C * ρ t + C * k * ∫ r in t..s, (‖α true r‖ + ‖α false r‖)) / g) =
        C ^ 2 * k * ρ t / g + C ^ 2 * k ^ 2 / g * ∫ r in t..s, (‖α true r‖ + ‖α false r‖) := by
      ring
    linarith
  -- the increments of `α_j`
  have hbd : ∀ j, ‖α j s - α j t‖ ≤
      K * (ε * L + k + k ^ 2 * L) * ((‖α true t‖ + ‖α false t‖) + ρ t) := by
    intro j
    have h1 := hA j s hs
    have hsplit2 : (∫ r in t..s, (C * ε * (‖α true r‖ + ‖α false r‖) + C * k * ρ r)) =
        C * ε * (∫ r in t..s, (‖α true r‖ + ‖α false r‖)) + C * k * (∫ r in t..s, ρ r) := by
      rw [intervalIntegral.integral_add
          ((intervalIntegrable_of_cont hXc hs).const_mul (C * ε))
          ((intervalIntegrable_of_cont hρc hs).const_mul (C * k)),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hT1 : C * ε * ∫ r in t..s, (‖α true r‖ + ‖α false r‖) ≤
        C * ε * (L * (blockK1 C g B * ((‖α true t‖ + ‖α false t‖) + ρ t))) :=
      mul_le_mul_of_nonneg_left hI_le (mul_nonneg hC.le hε)
    have hT3 : C ^ 2 * k ^ 2 / g * ∫ r in t..s, (‖α true r‖ + ‖α false r‖) ≤
        C ^ 2 * k ^ 2 / g * (L * (blockK1 C g B * ((‖α true t‖ + ‖α false t‖) + ρ t))) :=
      mul_le_mul_of_nonneg_left hI_le
        (div_nonneg (mul_nonneg (sq_nonneg C) (sq_nonneg k)) hg.le)
    have hT2 : C ^ 2 * k * ρ t / g ≤ C ^ 2 * k * ((‖α true t‖ + ‖α false t‖) + ρ t) / g := by
      gcongr
    have hp : 0 ≤ C * blockK1 C g B := mul_nonneg hC.le hK1
    have hq : 0 ≤ C ^ 2 / g := div_nonneg (sq_nonneg C) hg.le
    have hr : 0 ≤ C ^ 2 * blockK1 C g B / g :=
      div_nonneg (mul_nonneg (sq_nonneg C) hK1) hg.le
    have ha : 0 ≤ ε * L := mul_nonneg hε hL
    have hb : 0 ≤ k := hk
    have hc' : 0 ≤ k ^ 2 * L := mul_nonneg (sq_nonneg k) hL
    have hsum : (C * blockK1 C g B) * (ε * L) + (C ^ 2 / g) * k + (C ^ 2 * blockK1 C g B / g) *
        (k ^ 2 * L) ≤ (C * blockK1 C g B + C ^ 2 / g + C ^ 2 * blockK1 C g B / g) *
          (ε * L + k + k ^ 2 * L) := by
      nlinarith [mul_nonneg hp hb, mul_nonneg hp hc', mul_nonneg hq ha, mul_nonneg hq hc',
        mul_nonneg hr ha, mul_nonneg hr hb]
    have hK2eq : blockK2 C g B = C * blockK1 C g B + C ^ 2 / g + C ^ 2 * blockK1 C g B / g := rfl
    have hKK : (C * blockK1 C g B + C ^ 2 / g + C ^ 2 * blockK1 C g B / g) *
        (ε * L + k + k ^ 2 * L) ≤ K * (ε * L + k + k ^ 2 * L) := by
      rw [← hK2eq]
      exact mul_le_mul_of_nonneg_right hK2K
        (add_nonneg (add_nonneg (mul_nonneg hε hL) hk) (mul_nonneg (sq_nonneg k) hL))
    have hkey := mul_le_mul_of_nonneg_right (le_trans hsum hKK) hS0
    have hD : C * ε * (∫ r in t..s, (‖α true r‖ + ‖α false r‖)) + C * k * (∫ r in t..s, ρ r) ≤
        K * (ε * L + k + k ^ 2 * L) * ((‖α true t‖ + ‖α false t‖) + ρ t) := by
      simp only [div_eq_mul_inv] at hPk hT2 hT3 hkey ⊢
      linarith [hsplit2, hPk, hT1, hT2, hT3, hkey]
    linarith [h1, hsplit2, hD]
  -- the complement, part (3)
  have hJbound : ∫ r in t..s, Real.exp (-g * (s - r)) * (‖α true r‖ + ‖α false r‖) ≤
      blockK1 C g B * ((‖α true t‖ + ‖α false t‖) + ρ t) * (1 / g) := by
    have hJi : IntervalIntegrable
        (fun r => Real.exp (-g * (s - r)) * (‖α true r‖ + ‖α false r‖)) volume t s :=
      ContinuousOn.intervalIntegrable (by
        rw [Set.uIcc_of_le hts]
        exact (Continuous.continuousOn (by fun_prop :
          Continuous (fun r : ℝ => Real.exp (-g * (s - r))))).mul hXs)
    have hCi : IntervalIntegrable
        (fun r => (blockK1 C g B * ((‖α true t‖ + ‖α false t‖) + ρ t)) * Real.exp (-g * (s - r)))
        volume t s :=
      Continuous.intervalIntegrable (by fun_prop) t s
    have hm := intervalIntegral.integral_mono_on hts hJi hCi (fun r hr => by
      have hc_r := hcr r ⟨hr.1, hr.2⟩
      have := mul_le_mul_of_nonneg_left hc_r (Real.exp_pos (-g * (s - r))).le
      linarith)
    rw [intervalIntegral.integral_const_mul] at hm
    have hEx2 := integral_exp_neg_sub_le hg hts
    have h := mul_le_mul_of_nonneg_left hEx2 hK1S0
    linarith
  have hr3 := hR s hs
  have hJs := hJbound
  have hkJ : C * k * ∫ r in t..s, Real.exp (-g * (s - r)) * (‖α true r‖ + ‖α false r‖) ≤
      C * k * (blockK1 C g B * ((‖α true t‖ + ‖α false t‖) + ρ t) * (1 / g)) :=
    mul_le_mul_of_nonneg_left hJs (mul_nonneg hC.le hk)
  have hnn : 0 ≤ Real.exp (-g * (s - t)) * ρ t + k * ((‖α true t‖ + ‖α false t‖) + ρ t) :=
    add_nonneg (mul_nonneg (Real.exp_pos _).le hρt) (mul_nonneg hk hS0)
  have hX3 : blockK3 C g B * (Real.exp (-g * (s - t)) * ρ t +
      k * ((‖α true t‖ + ‖α false t‖) + ρ t)) ≤
      K * (Real.exp (-g * (s - t)) * ρ t + k * ((‖α true t‖ + ‖α false t‖) + ρ t)) :=
    mul_le_mul_of_nonneg_right hK3K hnn
  have hmain : C * Real.exp (-g * (s - t)) * ρ t +
      C * k * (blockK1 C g B * ((‖α true t‖ + ‖α false t‖) + ρ t) * (1 / g)) ≤
      blockK3 C g B * (Real.exp (-g * (s - t)) * ρ t +
        k * ((‖α true t‖ + ‖α false t‖) + ρ t)) := by
    have e : blockK3 C g B * (Real.exp (-g * (s - t)) * ρ t +
        k * ((‖α true t‖ + ‖α false t‖) + ρ t)) =
        C * Real.exp (-g * (s - t)) * ρ t +
          C * k * (blockK1 C g B * ((‖α true t‖ + ‖α false t‖) + ρ t) * (1 / g)) +
          C * k * ((‖α true t‖ + ‖α false t‖) + ρ t) +
          C * blockK1 C g B / g * (Real.exp (-g * (s - t)) * ρ t) := by
      unfold blockK3
      ring
    have ha1 : 0 ≤ C * k * ((‖α true t‖ + ‖α false t‖) + ρ t) :=
      mul_nonneg (mul_nonneg hC.le hk) hS0
    have ha2 : 0 ≤ C * blockK1 C g B / g * (Real.exp (-g * (s - t)) * ρ t) :=
      mul_nonneg (div_nonneg (mul_nonneg hC.le hK1) hg.le) (mul_nonneg (Real.exp_pos _).le hρt)
    linarith
  have p3 : ρ s ≤ K * (Real.exp (-g * (s - t)) * ρ t + k * ((‖α true t‖ + ‖α false t‖) + ρ t)) := by
    linarith [hr3, hkJ, hmain, hX3]
  exact ⟨p1, hbd, p3⟩

end UnforcedLeray.Short.PartIIIb
