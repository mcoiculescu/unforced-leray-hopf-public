import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_7_4

/-!
# Part II-b, organize task `PartII-b:G4/5/2/1/2/org`: weighted jets of the inlet profile

Source of record: `the November 2 reference manuscript`, lines 2316-2318 (age
cutoff equal to one near zero and zero before the terminal time), 2356-2358 (the periodized
stream and every fixed derivative have exponential transverse decay, with polynomial `c` costs),
2360-2366 (`e_ε = e_0 + ε e_1` of the cut stream `χ(s)ψ`), 2386-2387 (`W^{j,∞}` bounds).

`InletProfileWeightedJets` (`Sub/PartII-b_G4_5_2.lean`) is assembled from the existing leaves
`CutStreamJets` (accepted, `PartII-b:G4/5/2/2/3`), `RingStreamJetsDecay` (`PartII-b:G4/3/7/4/1`,
decay-preserving ring-stream Leibniz, decay rate halved), `InletProfileSmoothVanish` (accepted,
`PartII-b:G4/5/2/2/5`) and `CutStreamSVanish` (accepted as `PartII-b:G4/3/7/4/2`): the inlet profile
jets of order `≤ j` are `≤ A e^{-(κ/2)|η|/c}`, `A ≲ ν^{-(3+2N)}` (as in `inletJetDecay_of`), and
`(1+t)^w e^{-(κ/2)t/c} ≤ e · w! · (1 + 2c/κ)^w ≤ e · w! (1+2/κ)^w c^w` (`one_add_pow_mul_exp_le`),
`c = ν⁻²`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint UnforcedLeray.PhaseSpace
  UnforcedLeray.B0411 UnforcedLeray.B0412

namespace InletWeightAux

/-- `(1+t)^n e^{-a t} ≤ e · n! · (1 + a⁻¹)^n` for `a > 0`, `t ≥ 0` (`1 + t ≤ (1 + a⁻¹)(1 + at)` and
`(1+u)^n ≤ n! e^{1+u}`). -/
theorem one_add_pow_mul_exp_le (n : ℕ) {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    (1 + t) ^ n * Real.exp (-(a * t)) ≤ Real.exp 1 * n.factorial * (1 + a⁻¹) ^ n := by
  set u := a * t with hu
  have hu0 : 0 ≤ u := mul_nonneg ha.le ht
  have hai : 0 ≤ a⁻¹ := inv_nonneg.2 ha.le
  have h1 : 1 + t ≤ (1 + a⁻¹) * (1 + u) := by
    have e : t = a⁻¹ * u := by rw [hu, ← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
    nlinarith [mul_nonneg hai hu0]
  have h2 : (1 + t) ^ n ≤ (1 + a⁻¹) ^ n * (1 + u) ^ n := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) h1 n
  have h3 : (1 + u) ^ n ≤ n.factorial * Real.exp (1 + u) := by
    have h := Real.pow_div_factorial_le_exp (1 + u) (by linarith : (0 : ℝ) ≤ 1 + u) n
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    rw [div_le_iff₀ hf] at h
    linarith [mul_comm (Real.exp (1 + u)) (n.factorial : ℝ)]
  have h4 : Real.exp (1 + u) * Real.exp (-u) = Real.exp 1 := by
    rw [← Real.exp_add]; ring_nf
  have hp : 0 ≤ (1 + a⁻¹) ^ n := by positivity
  calc (1 + t) ^ n * Real.exp (-u)
      ≤ ((1 + a⁻¹) ^ n * (1 + u) ^ n) * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ ≤ ((1 + a⁻¹) ^ n * (n.factorial * Real.exp (1 + u))) * Real.exp (-u) := by
        gcongr
    _ = (1 + a⁻¹) ^ n * n.factorial * (Real.exp (1 + u) * Real.exp (-u)) := by ring
    _ = Real.exp 1 * n.factorial * (1 + a⁻¹) ^ n := by rw [h4]; ring

end InletWeightAux

/-- **Assembly of `InletProfileWeightedJets`** (SP 2356-2366, 2386-2387). -/
theorem inletProfileWeightedJets_of (h3 : CutStreamJets) (h4 : RingStreamJetsDecay)
    (h5 : InletProfileSmoothVanish) (h6 : CutStreamSVanish) : InletProfileWeightedJets := by
  intro Sig lam q hSig hq dm dp hdm j w
  obtain ⟨C3, κ, N, hC3, hκ, h3'⟩ := h3 lam q hq (j + 1)
  obtain ⟨C4, hC4, h4'⟩ := h4 j
  obtain ⟨ν₀, hν₀, h5'⟩ := h5 Sig lam q hSig hq dm dp hdm
  set W : ℝ := Real.exp 1 * w.factorial * (1 + 2 / κ) ^ w with hW
  set K : ℝ := C4 * (1 + Sig) * (1 + 1 / κ) * (C3 * (1 + 1 / Sig) ^ (j + 1)) * W with hK
  have hWpos : 0 < W := by positivity
  have hKpos : 0 < K := by positivity
  refine ⟨K, 3 + 2 * N + 2 * w, min ν₀ 1, hKpos, lt_min hν₀ one_pos, ?_⟩
  intro p d hreg hν hSig' hmode i
  have hν0 : p.ν ≤ ν₀ := hν.trans (min_le_left _ _)
  have hν1 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  have hνpos : 0 < p.ν := p.ν_pos
  obtain ⟨hsm, hvan⟩ := h5' p d hreg hν0 hSig' hmode i
  refine ⟨hsm, hvan, ?_⟩
  have hH : 0 < p.H := p.H_pos
  have hc1 : 1 ≤ p.c := by
    rw [hreg.c_eq, one_le_inv₀ (by positivity)]
    nlinarith
  have hR1 : 1 ≤ p.R := by
    have hε : p.ε ≤ 1 := by
      rw [hreg.eps_eq]
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ d / p.ν := div_nonneg (by linarith [hreg.dm_pos, hreg.dm_le]) hνpos.le
      rw [neg_div]; linarith
    show 1 ≤ p.ε⁻¹
    exact one_le_inv₀ p.ε_pos |>.mpr hε
  have hHe : p.H = Sig / p.ν := by rw [Params.H, hSig']
  obtain ⟨hcutsm, hcut⟩ := h3' p hmode hc1 hH i
  have hcpos : 0 < p.c := by linarith
  set M : ℝ := C3 * (1 + p.H⁻¹) ^ (j + 1) * p.c ^ N with hM
  have hM0 : 0 ≤ M := by positivity
  have hring := h4' p.R (p.H / 2) p.c κ M (p.cutStream i) hR1 (by positivity) hcpos hκ hM0
    hcutsm
    (by
      intro x hx
      unfold Params.cutStream
      simp [ageCutoff_eq_zero hH (show p.H / 2 ≤ x.1 from hx.le)])
    (fun x hx => h6 lam q hq p hmode hc1 hH i x hx)
    (fun l hl x => hcut l hl x)
  intro l hl x
  have hmain : ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ ≤
      C4 * (1 + p.H / 2) * (1 + p.c / κ) * M * Real.exp (-((κ / 2) * |x.2.2| / p.c)) :=
    hring l hl x
  -- the transverse weight against the halved exponential decay
  have hwt : (1 + |x.2.2|) ^ w * Real.exp (-((κ / 2) * |x.2.2| / p.c)) ≤ W * p.c ^ w := by
    have ha : 0 < κ / 2 / p.c := by positivity
    have e : -((κ / 2) * |x.2.2| / p.c) = -((κ / 2 / p.c) * |x.2.2|) := by ring
    rw [e]
    have h := InletWeightAux.one_add_pow_mul_exp_le w ha (abs_nonneg x.2.2)
    have hinv : (κ / 2 / p.c)⁻¹ = 2 * p.c / κ := by field_simp
    rw [hinv] at h
    have hb : 1 + 2 * p.c / κ ≤ (1 + 2 / κ) * p.c := by
      have e2 : 2 * p.c / κ = (2 / κ) * p.c := by ring
      rw [e2]
      nlinarith [mul_nonneg (div_pos two_pos hκ).le (by linarith : (0 : ℝ) ≤ p.c - 1)]
    calc _ ≤ Real.exp 1 * w.factorial * (1 + 2 * p.c / κ) ^ w := h
      _ ≤ Real.exp 1 * w.factorial * ((1 + 2 / κ) * p.c) ^ w := by gcongr
      _ = W * p.c ^ w := by rw [hW, mul_pow]; ring
  set A : ℝ := C4 * (1 + p.H / 2) * (1 + p.c / κ) * M with hA
  have hA0 : 0 ≤ A := by positivity
  have hcomb : (1 + |x.2.2|) ^ w * ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ ≤
      A * (W * p.c ^ w) := by
    have hw0 : 0 ≤ (1 + |x.2.2|) ^ w := by positivity
    calc (1 + |x.2.2|) ^ w * ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖
        ≤ (1 + |x.2.2|) ^ w * (A * Real.exp (-((κ / 2) * |x.2.2| / p.c))) :=
          mul_le_mul_of_nonneg_left hmain hw0
      _ = A * ((1 + |x.2.2|) ^ w * Real.exp (-((κ / 2) * |x.2.2| / p.c))) := by ring
      _ ≤ A * (W * p.c ^ w) := mul_le_mul_of_nonneg_left hwt hA0
  have hS : 1 + p.H / 2 ≤ (1 + Sig) * p.ν⁻¹ := by
    rw [hHe]
    have h1 : (1 : ℝ) ≤ p.ν⁻¹ := one_le_inv₀ hνpos |>.mpr hν1
    have e : (1 + Sig) * p.ν⁻¹ = p.ν⁻¹ + Sig / p.ν := by rw [div_eq_mul_inv]; ring
    rw [e]
    nlinarith [div_nonneg hSig.le hνpos.le]
  have hcc : 1 + p.c / κ ≤ (1 + 1 / κ) * p.c := by
    have : p.c / κ = (1 / κ) * p.c := by rw [div_eq_mul_inv]; ring
    rw [this]; nlinarith [mul_nonneg (one_div_pos.2 hκ).le (by linarith : 0 ≤ p.c)]
  have hHi : 1 + p.H⁻¹ ≤ 1 + 1 / Sig := by
    have h1 : p.ν / Sig ≤ 1 / Sig := by gcongr
    have : p.H⁻¹ ≤ 1 / Sig := by
      rw [hHe, inv_div]; exact h1
    linarith
  have hMle : M ≤ C3 * (1 + 1 / Sig) ^ (j + 1) * p.c ^ N := by
    rw [hM]; gcongr
  have hcν : p.c = (p.ν ^ 2)⁻¹ := hreg.c_eq
  have hfin : A ≤ C4 * ((1 + Sig) * p.ν⁻¹) * ((1 + 1 / κ) * p.c) *
        (C3 * (1 + 1 / Sig) ^ (j + 1) * p.c ^ N) := by
    rw [hA]; gcongr
  have heq : C4 * ((1 + Sig) * p.ν⁻¹) * ((1 + 1 / κ) * p.c) *
        (C3 * (1 + 1 / Sig) ^ (j + 1) * p.c ^ N) * (W * p.c ^ w) =
      K * (p.ν ^ (3 + 2 * N + 2 * w))⁻¹ := by
    have e : (p.ν ^ (3 + 2 * N + 2 * w))⁻¹ =
        p.ν⁻¹ * (p.ν ^ 2)⁻¹ * ((p.ν ^ 2)⁻¹) ^ N * ((p.ν ^ 2)⁻¹) ^ w := by
      simp only [← inv_pow]; ring
    rw [e, hK, hcν]
    ring
  have hWc : 0 ≤ W * p.c ^ w := by positivity
  calc _ ≤ A * (W * p.c ^ w) := hcomb
    _ ≤ C4 * ((1 + Sig) * p.ν⁻¹) * ((1 + 1 / κ) * p.c) *
        (C3 * (1 + 1 / Sig) ^ (j + 1) * p.c ^ N) * (W * p.c ^ w) :=
        mul_le_mul_of_nonneg_right hfin hWc
    _ = _ := heq

end UnforcedLeray.Short.IIb
