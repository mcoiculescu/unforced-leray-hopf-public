import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_7

/-!
# Part II-b, task `PartII-b:G4/3/7/10`: the column envelope from its parts (`colEnvelope_of_parts`)

Source of record: `the November 2 reference manuscript` (SP) lines 2370-2374, 2385.
Conditional assembly of `ColEnvelope` from `RawProfJet`, `InletJetDecay`, `JetLe`, `VecDiffJet`,
`BEpsJet`, `ColVanish`. On `0 < s ≤ H/2` (`H = ageCut/ν`, so `1 + s ≤ (1+Σ) ν⁻¹`):
`colEpsR = s(∂_sF - ν vecDiffEps F + bEps F)`, each piece is bounded by the jets of the inlet
profile (`InletJetDecay`, `JetLe`, `VecDiffJet`) and of the raw profile (`RawProfJet`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete

theorem colEnv_mul3 {K T S B1 B2 : ℝ} (hK : 0 ≤ K) (hT0 : 0 ≤ T) (hS0 : 0 ≤ S)
    (hT : T ≤ B1) (hS : S ≤ B2) : K * T * S ≤ K * B1 * B2 :=
  mul_le_mul (mul_le_mul_of_nonneg_left hT hK) hS hS0 (mul_nonneg hK (hT0.trans hT))

theorem colEnv_chartJet_nonneg (G : Coord → Axi.Merid) (x : Coord) : 0 ≤ chartJet G x := by
  unfold chartJet
  positivity

set_option maxHeartbeats 1600000 in
/-- **The column envelope from its parts** (SP 2370-2374, 2385). -/
theorem colEnvelope_of_parts (hR : UnforcedLeray.Short.IIb.RawProfJet)
    (hJ : UnforcedLeray.Short.IIb.InletJetDecay) (hL : UnforcedLeray.Short.IIb.JetLe)
    (hV : UnforcedLeray.Short.IIb.VecDiffJet) (hB : UnforcedLeray.Short.IIb.BEpsJet)
    (hVan : UnforcedLeray.Short.IIb.ColVanish) : UnforcedLeray.Short.IIb.ColEnvelope := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨CR, kR, NR, νR, hCR, hνR, hνR1, HR⟩ := hR Sig hSig dm dp hdm
  obtain ⟨CJ, κ, kJ, νJ, hCJ, hκ, hνJ, hνJ1, HJ⟩ := hJ Sig lam q hSig hq dm dp hdm
  obtain ⟨KL, hKL, HL⟩ := hL
  obtain ⟨KV, hKV, HV⟩ := hV
  obtain ⟨νV, hνV, HVan⟩ := hVan Sig lam q hSig hq dm dp hdm
  have ha : 0 < 1 + Sig := by linarith
  have hc1 : 0 ≤ 2 * KL * CJ * (1 + Sig) := (mul_pos (mul_pos (mul_pos two_pos hKL) hCJ) ha).le
  have hc2 : 0 ≤ 3 * KV * CJ * (1 + Sig) ^ 2 :=
    (mul_pos (mul_pos (mul_pos (by norm_num) hKV) hCJ) (pow_pos ha 2)).le
  have hc3 : 0 ≤ 12 * CR * KL * CJ * (1 + Sig) :=
    (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) hCR) hKL) hCJ) ha).le
  refine ⟨2 * KL * CJ * (1 + Sig) + 3 * KV * CJ * (1 + Sig) ^ 2 + 12 * CR * KL * CJ * (1 + Sig),
    κ, kR + kJ + 2, NR + 2, min (min νR νJ) νV, ?_, hκ, lt_min (lt_min hνR hνJ) hνV,
    ((min_le_left _ _).trans (min_le_left _ _)).trans hνR1, ?_⟩
  · have h1 : 0 < 2 * KL * CJ * (1 + Sig) := mul_pos (mul_pos (mul_pos two_pos hKL) hCJ) ha
    have h2 : 0 < 3 * KV * CJ * (1 + Sig) ^ 2 :=
      mul_pos (mul_pos (mul_pos (by norm_num) hKV) hCJ) (pow_pos ha 2)
    have h3 : 0 < 12 * CR * KL * CJ * (1 + Sig) :=
      mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) hCR) hKL) hCJ) ha
    linarith
  intro p d hreg i
  obtain ⟨hB0, hν, hS, hm⟩ := hreg
  have hνpos : 0 < p.ν := p.ν_pos
  have h0 : p.ν ≤ νR := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have h1 : p.ν ≤ νJ := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have h2 : p.ν ≤ νV := hν.trans (min_le_right _ _)
  have hν1 : p.ν ≤ 1 := h0.trans hνR1
  have hdpos : 0 < d := lt_of_lt_of_le hB0.dm_pos hB0.dm_le
  have hεlo : 0 ≤ p.ε := by
    rw [hB0.eps_eq]
    exact (Real.exp_pos _).le
  have hεhi : p.ε ≤ 1 := by
    rw [hB0.eps_eq]
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hνpos.le
  refine ⟨?_, ?_⟩
  · intro x hx
    exact HVan p d ⟨hB0, h2, hS, hm⟩ i x hx
  · intro x hx0 hxH
    have hHpos : 0 < p.H := p.H_pos
    have hxHle : x.1 ≤ p.H := by linarith
    obtain ⟨-, -, hRx⟩ := HR p d hB0 h0 hS x hx0 hxHle
    obtain ⟨hFsm, hDer⟩ := HJ p d ⟨hB0, h1, hS, hm⟩ i
    have hLx := HL (p.inletProfile i) hFsm x
    have hVx := HV p.ε hεlo hεhi (p.inletProfile i) hFsm x
    have hBx := hB p hεlo hεhi (p.inletProfile i) x
    -- decomposition of the column on `s > 0`
    have hdec : ‖colEpsR p i x‖ ≤ x.1 * ‖Axi.dS (p.inletProfile i) x‖ +
        x.1 * (p.ν * ‖vecDiffEps p.ε (p.inletProfile i) x‖) + x.1 * ‖bEps p (p.inletProfile i) x‖ := by
      unfold colEpsR colDiffR colIntR
      rw [if_pos hx0]
      have e1 := norm_add_le
        (x.1 • (Axi.dS (p.inletProfile i) x - p.ν • vecDiffEps p.ε (p.inletProfile i) x))
        (x.1 • bEps p (p.inletProfile i) x)
      have e3 := norm_sub_le (Axi.dS (p.inletProfile i) x)
        (p.ν • vecDiffEps p.ε (p.inletProfile i) x)
      have e4 : ‖p.ν • vecDiffEps p.ε (p.inletProfile i) x‖ =
          p.ν * ‖vecDiffEps p.ε (p.inletProfile i) x‖ := by
        rw [norm_smul, Real.norm_of_nonneg hνpos.le]
      have e5 : ‖x.1 • (Axi.dS (p.inletProfile i) x - p.ν • vecDiffEps p.ε (p.inletProfile i) x)‖ =
          x.1 * ‖Axi.dS (p.inletProfile i) x - p.ν • vecDiffEps p.ε (p.inletProfile i) x‖ := by
        rw [norm_smul, Real.norm_of_nonneg hx0.le]
      have e6 : ‖x.1 • bEps p (p.inletProfile i) x‖ = x.1 * ‖bEps p (p.inletProfile i) x‖ := by
        rw [norm_smul, Real.norm_of_nonneg hx0.le]
      have e7 := mul_le_mul_of_nonneg_left e3 hx0.le
      rw [e4] at e7
      linarith
    -- sums of the derivatives of the inlet profile
    have hS1 : ∑ l ∈ Finset.range 2, ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ ≤
        2 * (CJ * (p.ν⁻¹) ^ kJ * Real.exp (-(κ * |x.2.2| / p.c))) := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      have a0 := hDer 0 (by norm_num) x
      have a1 := hDer 1 (by norm_num) x
      rw [← inv_pow] at a0 a1
      nlinarith
    have hS2 : ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ ≤
        3 * (CJ * (p.ν⁻¹) ^ kJ * Real.exp (-(κ * |x.2.2| / p.c))) := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      have a0 := hDer 0 (by norm_num) x
      have a1 := hDer 1 (by norm_num) x
      have a2 := hDer 2 (by norm_num) x
      rw [← inv_pow] at a0 a1 a2
      nlinarith
    have hS1nn : 0 ≤ ∑ l ∈ Finset.range 2, ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ :=
      Finset.sum_nonneg (fun l _ => norm_nonneg _)
    have hS2nn : 0 ≤ ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ :=
      Finset.sum_nonneg (fun l _ => norm_nonneg _)
    -- the scalar factor `1 + |s| + |η| ≤ (1 + Σ) ν⁻¹ (1 + |η|)`
    have hHν : p.H * p.ν = Sig := by
      show p.ageCut / p.ν * p.ν = Sig
      rw [div_mul_cancel₀ _ hνpos.ne', hS]
    have hxν : x.1 * p.ν ≤ Sig / 2 := by
      have := mul_le_mul_of_nonneg_right hxH hνpos.le
      linarith
    have hg' : 1 + x.1 ≤ (1 + Sig) * p.ν⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hνpos]
      nlinarith
    have hT : 1 + |x.1| + |x.2.2| ≤ (1 + Sig) * p.ν⁻¹ * (1 + |x.2.2|) := by
      rw [abs_of_pos hx0]
      have h1' := mul_le_mul_of_nonneg_right hg' (by positivity : (0:ℝ) ≤ 1 + |x.2.2|)
      have h2' : (1 + x.1) * (1 + |x.2.2|) = 1 + x.1 + |x.2.2| + x.1 * |x.2.2| := by ring
      linarith [mul_nonneg hx0.le (abs_nonneg x.2.2)]
    have hTnn : 0 ≤ 1 + |x.1| + |x.2.2| := by positivity
    -- chart-jet bounds
    have hcJ := colEnv_chartJet_nonneg (p.inletProfile i) x
    have hcR := colEnv_chartJet_nonneg (rawProf p) x
    rw [← inv_pow] at hRx
    have hdS2 : ‖Axi.dS (p.inletProfile i) x‖ ≤
        KL * ((1 + Sig) * p.ν⁻¹ * (1 + |x.2.2|)) *
          (2 * (CJ * (p.ν⁻¹) ^ kJ * Real.exp (-(κ * |x.2.2| / p.c)))) := by
      have hJF : chartJet (p.inletProfile i) x + ‖Axi.dS (p.inletProfile i) x‖ ≤
          KL * (1 + |x.1| + |x.2.2|) * ∑ l ∈ Finset.range 2, ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ := hLx
      have := colEnv_mul3 hKL.le hTnn hS1nn hT hS1
      linarith
    have hJF2 : chartJet (p.inletProfile i) x ≤
        KL * ((1 + Sig) * p.ν⁻¹ * (1 + |x.2.2|)) *
          (2 * (CJ * (p.ν⁻¹) ^ kJ * Real.exp (-(κ * |x.2.2| / p.c)))) := by
      have hJF : chartJet (p.inletProfile i) x + ‖Axi.dS (p.inletProfile i) x‖ ≤
          KL * (1 + |x.1| + |x.2.2|) * ∑ l ∈ Finset.range 2, ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ := hLx
      have := colEnv_mul3 hKL.le hTnn hS1nn hT hS1
      linarith [norm_nonneg (Axi.dS (p.inletProfile i) x)]
    have hV2 : ‖vecDiffEps p.ε (p.inletProfile i) x‖ ≤
        KV * ((1 + Sig) * p.ν⁻¹ * (1 + |x.2.2|)) ^ 2 *
          (3 * (CJ * (p.ν⁻¹) ^ kJ * Real.exp (-(κ * |x.2.2| / p.c)))) :=
      hVx.trans (colEnv_mul3 hKV.le (by positivity) hS2nn (pow_le_pow_left₀ hTnn hT 2) hS2)
    have hB2 : ‖bEps p (p.inletProfile i) x‖ ≤
        6 * (CR * (p.ν⁻¹) ^ kR * (1 + |x.2.2|) ^ NR) *
          (KL * ((1 + Sig) * p.ν⁻¹ * (1 + |x.2.2|)) *
            (2 * (CJ * (p.ν⁻¹) ^ kJ * Real.exp (-(κ * |x.2.2| / p.c))))) :=
      hBx.trans (mul_le_mul (mul_le_mul_of_nonneg_left hRx (by norm_num)) hJF2 hcJ
        (mul_nonneg (by norm_num) (hcR.trans hRx)))
    -- final assembly
    have hg0 : 0 < p.ν⁻¹ := inv_pos.mpr hνpos
    have hg1 : 1 ≤ p.ν⁻¹ := (one_le_inv₀ hνpos).mpr hν1
    have ht1 : 1 ≤ 1 + |x.2.2| := by linarith [abs_nonneg x.2.2]
    have ht0 : 0 ≤ 1 + |x.2.2| := by linarith [abs_nonneg x.2.2]
    have hE0 : 0 ≤ Real.exp (-(κ * |x.2.2| / p.c)) := (Real.exp_pos _).le
    have hsx : 0 ≤ x.1 := hx0.le
    rw [← inv_pow]
    set g := p.ν⁻¹ with hgdef
    set t := 1 + |x.2.2| with htdef
    set E := Real.exp (-(κ * |x.2.2| / p.c)) with hEdef
    have hgk1 : g ^ (kJ + 1) ≤ g ^ (kR + kJ + 2) := pow_le_pow_right₀ hg1 (by omega)
    have htN : t ≤ t ^ (NR + 2) := le_self_pow₀ ht1 (by omega)
    have hY1 : x.1 * ‖Axi.dS (p.inletProfile i) x‖ ≤
        (2 * KL * CJ * (1 + Sig)) * (x.1 * E) * (g ^ (kR + kJ + 2) * t ^ (NR + 2)) := by
      calc x.1 * ‖Axi.dS (p.inletProfile i) x‖
          ≤ x.1 * (KL * ((1 + Sig) * g * t) * (2 * (CJ * g ^ kJ * E))) :=
            mul_le_mul_of_nonneg_left hdS2 hsx
        _ = (2 * KL * CJ * (1 + Sig)) * (x.1 * E) * (g ^ (kJ + 1) * t) := by ring
        _ ≤ (2 * KL * CJ * (1 + Sig)) * (x.1 * E) * (g ^ (kR + kJ + 2) * t ^ (NR + 2)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hgk1 htN ht0 (pow_nonneg hg0.le _))
              (mul_nonneg hc1 (mul_nonneg hsx hE0))
    have hY2 : x.1 * (p.ν * ‖vecDiffEps p.ε (p.inletProfile i) x‖) ≤
        (3 * KV * CJ * (1 + Sig) ^ 2) * (x.1 * E) * (g ^ (kR + kJ + 2) * t ^ (NR + 2)) := by
      calc x.1 * (p.ν * ‖vecDiffEps p.ε (p.inletProfile i) x‖)
          ≤ x.1 * ‖vecDiffEps p.ε (p.inletProfile i) x‖ :=
            mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg _) hν1) hsx
        _ ≤ x.1 * (KV * ((1 + Sig) * g * t) ^ 2 * (3 * (CJ * g ^ kJ * E))) :=
            mul_le_mul_of_nonneg_left hV2 hsx
        _ = (3 * KV * CJ * (1 + Sig) ^ 2) * (x.1 * E) * (g ^ (kJ + 2) * t ^ 2) := by ring
        _ ≤ (3 * KV * CJ * (1 + Sig) ^ 2) * (x.1 * E) * (g ^ (kR + kJ + 2) * t ^ (NR + 2)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul (pow_le_pow_right₀ hg1 (by omega)) (pow_le_pow_right₀ ht1 (by omega))
                (pow_nonneg ht0 2) (pow_nonneg hg0.le _))
              (mul_nonneg hc2 (mul_nonneg hsx hE0))
    have hY3 : x.1 * ‖bEps p (p.inletProfile i) x‖ ≤
        (12 * CR * KL * CJ * (1 + Sig)) * (x.1 * E) * (g ^ (kR + kJ + 2) * t ^ (NR + 2)) := by
      calc x.1 * ‖bEps p (p.inletProfile i) x‖
          ≤ x.1 * (6 * (CR * g ^ kR * t ^ NR) * (KL * ((1 + Sig) * g * t) *
              (2 * (CJ * g ^ kJ * E)))) := mul_le_mul_of_nonneg_left hB2 hsx
        _ = (12 * CR * KL * CJ * (1 + Sig)) * (x.1 * E) * (g ^ (kR + kJ + 1) * t ^ (NR + 1)) := by
            ring
        _ ≤ (12 * CR * KL * CJ * (1 + Sig)) * (x.1 * E) * (g ^ (kR + kJ + 2) * t ^ (NR + 2)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul (pow_le_pow_right₀ hg1 (by omega)) (pow_le_pow_right₀ ht1 (by omega))
                (pow_nonneg ht0 _) (pow_nonneg hg0.le _))
              (mul_nonneg hc3 (mul_nonneg hsx hE0))
    calc ‖colEpsR p i x‖
        ≤ x.1 * ‖Axi.dS (p.inletProfile i) x‖ +
            x.1 * (p.ν * ‖vecDiffEps p.ε (p.inletProfile i) x‖) +
            x.1 * ‖bEps p (p.inletProfile i) x‖ := hdec
      _ ≤ (2 * KL * CJ * (1 + Sig)) * (x.1 * E) * (g ^ (kR + kJ + 2) * t ^ (NR + 2)) +
            (3 * KV * CJ * (1 + Sig) ^ 2) * (x.1 * E) * (g ^ (kR + kJ + 2) * t ^ (NR + 2)) +
            (12 * CR * KL * CJ * (1 + Sig)) * (x.1 * E) * (g ^ (kR + kJ + 2) * t ^ (NR + 2)) :=
            add_le_add (add_le_add hY1 hY2) hY3
      _ = (2 * KL * CJ * (1 + Sig) + 3 * KV * CJ * (1 + Sig) ^ 2 + 12 * CR * KL * CJ * (1 + Sig)) *
            g ^ (kR + kJ + 2) * x.1 * t ^ (NR + 2) * E := by ring

end UnforcedLeray.Short.IIb

end
