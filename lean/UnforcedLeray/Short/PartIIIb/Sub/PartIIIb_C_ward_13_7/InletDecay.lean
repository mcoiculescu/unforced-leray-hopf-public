import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_7.L1
import UnforcedLeray.Short.PartIIb.Tasks.StrongLateCoeff.NvFderiv
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.InletJetDecay
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletProfileJets.SmoothVanish

/-!
# Inverse-distance decay of the inlet columns (task `PartIII-b:C/ward/13/7/1/2`)

Source of record: `the November 2 reference manuscript`, 2563-2601, 2607-2608.
The inlet profile `b = p.inletProfile i` is smooth, vanishes for `s > H/2` and has jets of order
`≤ 1` bounded by `K e^{-κ|η|/c}` (`IIb.inletJetDecay`, `IIb.inletProfileSmoothVanish`).  With
`NvFderivBound` this gives `‖E_i y‖, ‖DE_i y‖ ≤ C (1+|y|)⁻¹` (far field: `E_i = 0` near the axis).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff
open UnforcedLeray.Cons.C03.Concrete (Params)

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem poly_exp_bound {a : ℝ} (ha : 0 < a) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, 0 ≤ t → (1 + t) ^ 2 * Real.exp (-(a * t)) ≤ M := by
  set m : ℝ := max 1 (2 / a) with hm
  have hm1 : 1 ≤ m := le_max_left _ _
  have hm2 : 2 / a ≤ m := le_max_right _ _
  have hma : 2 ≤ m * a := by
    have := (div_le_iff₀ ha).1 hm2
    linarith
  refine ⟨m ^ 2, by positivity, fun t ht => ?_⟩
  have h1 : 1 + t ≤ m * (1 + a * t / 2) := by nlinarith
  have h2 : 1 + a * t / 2 ≤ Real.exp (a * t / 2) := by
    have := Real.add_one_le_exp (a * t / 2)
    linarith
  have h3 : 1 + t ≤ m * Real.exp (a * t / 2) := h1.trans (by gcongr)
  have h4 : (1 + t) ^ 2 ≤ m ^ 2 * Real.exp (a * t) := by
    calc (1 + t) ^ 2 ≤ (m * Real.exp (a * t / 2)) ^ 2 := by gcongr
      _ = m ^ 2 * Real.exp (a * t) := by
        rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  calc (1 + t) ^ 2 * Real.exp (-(a * t)) ≤ m ^ 2 * Real.exp (a * t) * Real.exp (-(a * t)) := by
        gcongr
    _ = m ^ 2 := by rw [mul_assoc, ← Real.exp_add]; simp

theorem geom_ring {R : ℝ} (hR : 0 < R) {y : Space} (hy : y ∉ axis) :
    (1 + ‖y‖) * √(age R y) ≤ √(age R y) + R + |Axi.trans R y| ∧
    (1 + ‖y‖) * age R y ≤ age R y + R * √(age R y) + √(age R y) * |Axi.trans R y| := by
  have hρ := ϱ_pos hy
  have hsq : √(age R y) = R / ϱ y := sqrt_age hR hy
  set s' := √(age R y) with hs'
  have hs'0 : 0 ≤ s' := Real.sqrt_nonneg _
  have hage : age R y = s' ^ 2 := (Real.sq_sqrt (age_nonneg R y)).symm
  have h1 : ϱ y * s' = R := by rw [hsq]; field_simp
  have htr : |Axi.trans R y| = R * |y 2| / ϱ y := by
    unfold Axi.trans
    rw [abs_div, abs_mul, abs_of_pos hR, abs_of_pos hρ]
  have h2 : |y 2| * s' = |Axi.trans R y| := by rw [htr, hsq]; field_simp
  have hn : ‖y‖ ≤ ϱ y + |y 2| := by
    have h := norm_sq_eq_ϱ_sq_add y
    by_contra hc
    push_neg at hc
    nlinarith [norm_nonneg y, abs_nonneg (y 2), sq_abs (y 2), ϱ_nonneg y]
  have hn' : (1 + ‖y‖) * s' ≤ (1 + ϱ y + |y 2|) * s' :=
    mul_le_mul_of_nonneg_right (by linarith) hs'0
  constructor
  · nlinarith
  · rw [hage]
    have : (1 + ‖y‖) * s' ^ 2 ≤ (1 + ϱ y + |y 2|) * s' * s' := by
      rw [sq, ← mul_assoc]; exact mul_le_mul_of_nonneg_right hn' hs'0
    nlinarith

theorem Nv_eq_zero_of_lt {R S : ℝ} (hR : 0 < R) (hS : 0 < S) {b : ℝ × (ℝ × ℝ) → Merid}
    (hvan : ∀ x : ℝ × (ℝ × ℝ), S < x.1 → b x = 0) (τ : ℝ) {y : Space}
    (hy : ϱ y < R / √S) : Nv R b τ y = 0 := by
  by_cases hax : y ∈ axis
  · have h0 : ϱ y = 0 := (mem_axis_iff y).1 hax
    simp [Nv, age, h0]
  · have hρ := ϱ_pos hax
    have hsS : 0 < √S := Real.sqrt_pos.2 hS
    have h1 : ϱ y * √S < R := by rwa [lt_div_iff₀ hsS] at hy
    have h2 : (ϱ y * √S) ^ 2 < R ^ 2 := pow_lt_pow_left₀ h1 (by positivity) (by norm_num)
    rw [mul_pow, Real.sq_sqrt hS.le] at h2
    have hs : S < age R y := by
      unfold age
      rw [lt_div_iff₀ (pow_pos hρ 2)]
      linarith
    have hb0 : b (chart R τ y) = 0 := hvan _ hs
    simp [Nv, hb0]

theorem invDecay_Nv {R S κ c K : ℝ} (hR : 0 < R) (hS : 0 < S) (hκ : 0 < κ) (hc : 0 < c)
    (hK : 0 ≤ K) {b : ℝ × (ℝ × ℝ) → Merid} (hb : ContDiff ℝ ∞ b)
    (hvan : ∀ x : ℝ × (ℝ × ℝ), S < x.1 → b x = 0)
    (hb0 : ∀ x : ℝ × (ℝ × ℝ), ‖b x‖ ≤ K * Real.exp (-(κ * |x.2.2| / c)))
    (hb1 : ∀ x : ℝ × (ℝ × ℝ), ‖fderiv ℝ b x‖ ≤ K * Real.exp (-(κ * |x.2.2| / c))) :
    InvDecay (fun τ => Nv R b τ) := by
  have ha : 0 < κ / c := div_pos hκ hc
  obtain ⟨M, hM0, hM⟩ := poly_exp_bound ha
  have hexp : ∀ x : ℝ × (ℝ × ℝ), -(κ * |x.2.2| / c) = -(κ / c * |x.2.2|) := by
    intro x; ring
  set ε : ℝ := R⁻¹ with hε
  have hε0 : 0 ≤ ε := (inv_pos.2 hR).le
  set sS : ℝ := √S with hsS
  have hsS0 : 0 < sS := Real.sqrt_pos.2 hS
  set L : ℝ := S + R * sS + sS with hL
  set D : ℝ := 2 + ε * (2 * S + 2) + ε with hD
  have hL0 : 0 ≤ L := by positivity
  have hD0 : 0 ≤ D := by positivity
  set C : ℝ := max ((sS + R + 1) * (K * M)) (L * D * (K * M)) with hC
  have hC0 : 0 ≤ C := by positivity
  have hDiff : ∀ (τ : ℝ) (y : Space), DifferentiableAt ℝ (Nv R b τ) y := by
    intro τ y
    by_cases hV : ϱ y < R / sS
    · have hev : Nv R b τ =ᶠ[𝓝 y] fun _ => 0 := by
        have hopen : IsOpen {y' : Space | ϱ y' < R / sS} :=
          isOpen_lt continuous_ϱ continuous_const
        filter_upwards [hopen.mem_nhds hV] with y' hy'
        exact Nv_eq_zero_of_lt hR hS hvan τ hy'
      exact (differentiableAt_const (0 : Space)).congr_of_eventuallyEq hev
    · push_neg at hV
      have hy : y ∉ axis := by
        intro hax
        have := (mem_axis_iff y).1 hax
        have : 0 < R / sS := div_pos hR hsS0
        linarith
      exact (_root_.nvFderivBound R τ b y hR hy
        ((hb.differentiable (by simp)) _)).1
  refine ⟨C, hC0, fun τ => ⟨fun y => hDiff τ y, fun y => ?_⟩⟩
  have hpos : 0 < 1 + ‖y‖ := by positivity
  show ‖Nv R b τ y‖ ≤ C * (1 + ‖y‖)⁻¹ ∧ ‖fderiv ℝ (Nv R b τ) y‖ ≤ C * (1 + ‖y‖)⁻¹
  by_cases hV : ϱ y < R / sS
  · have hev : Nv R b τ =ᶠ[𝓝 y] fun _ => 0 := by
      have hopen : IsOpen {y' : Space | ϱ y' < R / sS} :=
        isOpen_lt continuous_ϱ continuous_const
      filter_upwards [hopen.mem_nhds hV] with y' hy'
      exact Nv_eq_zero_of_lt hR hS hvan τ hy'
    rw [Nv_eq_zero_of_lt hR hS hvan τ hV, hev.fderiv_eq]
    have : 0 ≤ C * (1 + ‖y‖)⁻¹ := by positivity
    refine ⟨?_, ?_⟩ <;> simpa using this
  · push_neg at hV
    have hy : y ∉ axis := by
      intro hax
      have := (mem_axis_iff y).1 hax
      have : 0 < R / sS := div_pos hR hsS0
      linarith
    have hs0 : 0 < age R y := age_pos hR.ne' hy
    have hsS' : age R y ≤ S := by
      have h1 : R ≤ ϱ y * sS := by rwa [div_le_iff₀ hsS0] at hV
      have h2 : R ^ 2 ≤ (ϱ y * sS) ^ 2 := pow_le_pow_left₀ hR.le h1 2
      rw [mul_pow, hsS, Real.sq_sqrt hS.le] at h2
      unfold age
      rw [div_le_iff₀ (pow_pos (ϱ_pos hy) 2)]
      linarith
    have hsq : √(age R y) ≤ sS := Real.sqrt_le_sqrt hsS'
    have hsq0 : 0 ≤ √(age R y) := Real.sqrt_nonneg _
    obtain ⟨g1, g2⟩ := geom_ring hR hy
    set t : ℝ := |Axi.trans R y| with ht
    have ht0 : 0 ≤ t := abs_nonneg _
    set x := chart R τ y with hx
    have hxs : x.1 = age R y := rfl
    have hxt : |x.2.2| = t := rfl
    set E : ℝ := K * Real.exp (-(κ / c * t)) with hE
    have hE0 : 0 ≤ E := by positivity
    have hb0x : ‖b x‖ ≤ E := by
      have := hb0 x
      rwa [hexp x, hxt] at this
    have hb1x : ‖fderiv ℝ b x‖ ≤ E := by
      have := hb1 x
      rwa [hexp x, hxt] at this
    have hpoly : (1 + t) ^ 2 * E ≤ K * M := by
      have := hM t ht0
      calc (1 + t) ^ 2 * E = K * ((1 + t) ^ 2 * Real.exp (-(κ / c * t))) := by rw [hE]; ring
        _ ≤ K * M := by gcongr
    have hpoly1 : (1 + t) * E ≤ K * M := by
      refine le_trans ?_ hpoly
      have : (1 + t) ≤ (1 + t) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right this hE0
    constructor
    · rw [norm_Nv R b τ hy, ← div_eq_mul_inv, le_div_iff₀ hpos]
      have h1 : √(age R y) * ‖b x‖ * (1 + ‖y‖) = ‖b x‖ * ((1 + ‖y‖) * √(age R y)) := by ring
      rw [h1]
      have h2 : ‖b x‖ * ((1 + ‖y‖) * √(age R y)) ≤ E * ((sS + R + 1) * (1 + t)) := by
        refine mul_le_mul hb0x (g1.trans ?_) (by positivity) hE0
        nlinarith [mul_nonneg hsS0.le ht0, mul_nonneg hR.le ht0]
      calc _ ≤ E * ((sS + R + 1) * (1 + t)) := h2
        _ = (sS + R + 1) * ((1 + t) * E) := by ring
        _ ≤ (sS + R + 1) * (K * M) := by gcongr
        _ ≤ C := le_max_left _ _
    · refine (_root_.nvFderivBound R τ b y hR hy
        ((hb.differentiable (by simp)) _)).2.trans ?_
      rw [← div_eq_mul_inv, le_div_iff₀ hpos]
      have hv : ∀ v : ℝ × (ℝ × ℝ), ‖v‖ ≤ 1 → ‖fderiv ℝ b x v‖ ≤ E := fun v hv =>
        (ContinuousLinearMap.le_opNorm _ _).trans
          ((mul_le_mul hb1x hv (norm_nonneg _) hE0).trans (by rw [mul_one]))
      have hn1 : ‖((0 : ℝ), ((0 : ℝ), (1 : ℝ)))‖ ≤ 1 := by simp [Prod.norm_def]
      have hn2 : ‖((0 : ℝ), ((1 : ℝ), (0 : ℝ)))‖ ≤ 1 := by simp [Prod.norm_def]
      have hn3 : ‖((1 : ℝ), ((0 : ℝ), (0 : ℝ)))‖ ≤ 1 := by simp [Prod.norm_def]
      have eEta : ‖dEta b x‖ ≤ E := hv _ hn1
      have eQ : ‖dQ b x‖ ≤ E := hv _ hn2
      have eS : ‖dS b x‖ ≤ E := hv _ hn3
      have eb0 : |b x 0| ≤ E := by
        have := PiLp.norm_apply_le (b x) 0
        rw [Real.norm_eq_abs] at this
        exact this.trans hb0x
      have hB : ‖dQ b x - ε • ((2 * x.1) • dS b x + x.2.2 • dEta b x + b x)‖ ≤
          E + ε * (2 * S * E + t * E + E) := by
        refine (norm_sub_le _ _).trans (add_le_add eQ ?_)
        rw [norm_smul, Real.norm_of_nonneg hε0]
        refine mul_le_mul_of_nonneg_left ?_ hε0
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) hb0x)
        · rw [norm_smul, Real.norm_eq_abs, abs_mul, hxs, abs_of_pos hs0]
          have : 2 * age R y ≤ 2 * S := by linarith
          calc _ ≤ (2 * S) * E := by
                rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
                exact mul_le_mul (by linarith) eS (norm_nonneg _) (by positivity)
            _ = _ := by ring
        · rw [norm_smul, Real.norm_eq_abs, hxt]
          exact mul_le_mul_of_nonneg_left eEta ht0
      have hbr : ‖dEta b x‖ + ‖dQ b x - ε • ((2 * x.1) • dS b x + x.2.2 • dEta b x + b x)‖ +
          ε * |b x 0| ≤ E * (D * (1 + t)) := by
        have : ε * |b x 0| ≤ ε * E := mul_le_mul_of_nonneg_left eb0 hε0
        have hh : E + (E + ε * (2 * S * E + t * E + E)) + ε * E ≤ E * (D * (1 + t)) := by
          have key : E * (D * (1 + t)) - (E + (E + ε * (2 * S * E + t * E + E)) + ε * E) =
              ε * E + E * t * (2 + 2 * ε * S + 2 * ε) := by rw [hD]; ring
          have : 0 ≤ ε * E + E * t * (2 + 2 * ε * S + 2 * ε) := by positivity
          linarith
        linarith
      have hG : UnforcedLeray.Short.IIb.gradProfileQuantity R⁻¹ b x ≤ age R y * (E * (D * (1 + t))) := by
        unfold UnforcedLeray.Short.IIb.gradProfileQuantity
        rw [hxs]
        exact mul_le_mul_of_nonneg_left hbr hs0.le
      have h3 : (1 + ‖y‖) * age R y ≤ L * (1 + t) := by
        refine g2.trans ?_
        have e1 : R * √(age R y) ≤ R * sS := mul_le_mul_of_nonneg_left hsq hR.le
        have e2 : √(age R y) * t ≤ sS * t := mul_le_mul_of_nonneg_right hsq ht0
        have e3 : 0 ≤ S * t := mul_nonneg hS.le ht0
        have e4 : 0 ≤ R * sS * t := by positivity
        have e5 : 0 ≤ sS := hsS0.le
        have key : L * (1 + t) = S + R * sS + sS + (S * t + R * sS * t + sS * t) := by
          rw [hL]; ring
        linarith
      calc UnforcedLeray.Short.IIb.gradProfileQuantity R⁻¹ b x * (1 + ‖y‖) ≤ age R y * (E * (D * (1 + t))) * (1 + ‖y‖) :=
            mul_le_mul_of_nonneg_right hG hpos.le
        _ = ((1 + ‖y‖) * age R y) * (D * (E * (1 + t))) := by ring
        _ ≤ (L * (1 + t)) * (D * (E * (1 + t))) :=
            mul_le_mul h3 le_rfl (by positivity) (by positivity)
        _ = L * D * ((1 + t) ^ 2 * E) := by ring
        _ ≤ L * D * (K * M) := by gcongr
        _ ≤ C := le_max_right _ _

/-- **Decay of the inlet columns at the levels of the contraction ball** (source 2563-2601,
2607-2608). -/
theorem inletDecayAtLevels : UnforcedLeray.Short.PartIIIb.Concrete.InletDecayAtLevels := by
  intro Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨C, κ, k, ν₁, hC, hκ, hν₁, -, hJ⟩ :=
    UnforcedLeray.Short.IIb.inletJetDecay Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₂, hν₂, hV⟩ :=
    UnforcedLeray.Short.IIb.inletProfileSmoothVanish Sig lam q hSig hq dm dp hdm
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, fun p d hreg hν hS hq' V rb pres hb hU i => ?_⟩
  have hνa : p.ν ≤ ν₁ := hν.trans (min_le_left _ _)
  have hνb : p.ν ≤ ν₂ := hν.trans (min_le_right _ _)
  have hcol : UnforcedLeray.Short.IIb.ColReg Sig q dm dp ν₁ p d := ⟨hreg, hνa, hS, hq'⟩
  obtain ⟨hcd, hjets⟩ := hJ p d hcol i
  obtain ⟨-, hvan⟩ := hV p d hreg hνb hS hq' i
  have hc : 0 < p.c := by
    rw [hreg.c_eq]; exact inv_pos.2 (pow_pos p.ν_pos 2)
  have hH2 : 0 < p.H / 2 := half_pos p.H_pos
  refine invDecay_Nv (K := C * (p.ν ^ k)⁻¹) p.R_pos hH2 hκ hc (by have := p.ν_pos; positivity)
    hcd hvan ?_ ?_
  · intro x
    have := hjets 0 (by norm_num) x
    rwa [norm_iteratedFDeriv_zero] at this
  · intro x
    have := hjets 1 (by norm_num) x
    rwa [norm_iteratedFDeriv_one] at this

end UnforcedLeray.Short.PartIIIb.Concrete
