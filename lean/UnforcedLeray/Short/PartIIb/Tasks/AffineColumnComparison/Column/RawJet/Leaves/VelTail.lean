import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_6_1

/-!
# Part II-b, task `PartII-b:G4/3/6/1/3`: the tail velocity jets `RawVelTailJets`

Source of record: `the November 2 reference manuscript`, `sct:transverse`
(lines 463-467) with the polynomial convention of lines 255-258.  The Part I input
`PartI.TrainTransverseTails` is applied with `ρ = 2`, `l = 0`, `S_ = Σ/ν`, and the four jets
`(ℓ,j) = (0,0),(1,0),(0,1),(2,0)` of `v`.  The train is transported from the period `p.c` to
`trainPeriod 2 ν = (ν²)⁻¹` along `BgRegime.c_eq`.  The polynomial `polyPS` is bounded by a power
of `ν⁻¹` for `ν ≤ 1`, with `t = ν⁻¹ ≥ 1`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace

/-- Transport of a BUC train along an equality of periods (only the velocity is kept). -/
theorem velTail_transport {ν c c' : ℝ} (h : c = c')
    (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hb : UnforcedLeray.Short.PartI.IsBUCTrain tr) :
    ∃ tr' : UnforcedLeray.B0140.TrainSol ν c',
      UnforcedLeray.Short.PartI.IsBUCTrain tr' ∧ tr'.v = tr.v := by
  subst h
  exact ⟨tr, hb, rfl⟩

/-- `trainPeriod 2 ν = (ν²)⁻¹`. -/
theorem velTail_trainPeriod_two {ν : ℝ} (hν : 0 < ν) :
    UnforcedLeray.Short.PartI.trainPeriod 2 ν = (ν ^ 2)⁻¹ := by
  unfold UnforcedLeray.Short.PartI.trainPeriod
  rw [Real.rpow_neg hν.le, Real.rpow_two]

/-- Exponent monotonicity of `ν ↦ (ν^a)⁻¹` on `(0, 1]`. -/
theorem velTail_inv_pow_mono {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) {a b : ℕ} (hab : a ≤ b) :
    (ν ^ a)⁻¹ ≤ (ν ^ b)⁻¹ :=
  inv_anti₀ (pow_pos hν b) (pow_le_pow_of_le_one hν.le hν1 hab)

/-- Pure arithmetic: for `t ≥ 1`, `C (Q)^N ≤ C (3(1+Sig))^N t^(3N)` with `Q = (1+t²+t)(1+Sig t)`. -/
theorem velTail_poly_bound (C Sig t : ℝ) (N : ℕ) (hC : 0 ≤ C) (hS : 0 ≤ Sig) (ht : 1 ≤ t) :
    C * ((1 + t ^ 2 + t) * (1 + Sig * t)) ^ N ≤ C * (3 * (1 + Sig)) ^ N * t ^ (3 * N) := by
  have ht0 : 0 ≤ t := by linarith
  have ha : 0 ≤ (t - 1) * t := mul_nonneg (by linarith) ht0
  have hb : 0 ≤ (t - 1) * t ^ 2 := mul_nonneg (by linarith) (by positivity)
  have h1 : 1 + t + t ^ 2 ≤ 3 * t ^ 3 := by nlinarith
  have h2 : t * (1 + t + t ^ 2) ≤ 3 * t ^ 3 := by nlinarith
  have hQ0 : 0 ≤ (1 + t ^ 2 + t) * (1 + Sig * t) := by positivity
  have hQ : (1 + t ^ 2 + t) * (1 + Sig * t) ≤ 3 * (1 + Sig) * t ^ 3 := by
    have h3 : Sig * (t * (1 + t + t ^ 2)) ≤ Sig * (3 * t ^ 3) :=
      mul_le_mul_of_nonneg_left h2 hS
    nlinarith
  have hpow : ((1 + t ^ 2 + t) * (1 + Sig * t)) ^ N ≤ (3 * (1 + Sig) * t ^ 3) ^ N :=
    pow_le_pow_left₀ hQ0 hQ N
  have heq : (3 * (1 + Sig) * t ^ 3) ^ N = (3 * (1 + Sig)) ^ N * t ^ (3 * N) := by
    rw [mul_pow, ← pow_mul]
  rw [heq] at hpow
  calc C * ((1 + t ^ 2 + t) * (1 + Sig * t)) ^ N
      ≤ C * ((3 * (1 + Sig)) ^ N * t ^ (3 * N)) := mul_le_mul_of_nonneg_left hpow hC
    _ = C * (3 * (1 + Sig)) ^ N * t ^ (3 * N) := by ring

/-- One tail jet, from `PartI.TrainTransverseTails` at `ρ = 2`, `l = 0`, `S_ = Σ/ν`.  The constant
`C'` does not depend on `Σ`, so it can be summed over the four jets. -/
theorem velTail_tailJet (hT : UnforcedLeray.Short.PartI.TrainTransverseTails) (ℓ j : ℕ) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ Sig : ℝ, 0 < Sig → ∃ (C : ℝ) (N : ℕ) (ν₀ : ℝ),
      0 < C ∧ 0 < ν₀ ∧ ν₀ ≤ 1 ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : UnforcedLeray.B0140.TrainSol ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν),
          UnforcedLeray.Short.PartI.IsBUCTrain tr →
          ∀ s : ℝ, 0 < s → s ≤ Sig / ν →
            ∀ z : UnforcedLeray.Cyl.Plane, C' / ν + 2 ≤ |z.2| →
              ‖UnforcedLeray.Short.PartI.ageJet ℓ j tr.v s z‖ ≤ C * (ν ^ N)⁻¹ := by
  obtain ⟨b, C₀, C', hb, hC₀, hC', C₁, N₁, ν₀₁, hC₁, hν₀₁, hT'⟩ :=
    hT 2 (by norm_num) ℓ j
  refine ⟨C', hC', fun Sig hSig => ⟨2 * C₁ * (3 * (1 + Sig)) ^ N₁, 3 * N₁, min ν₀₁ 1,
    mul_pos (mul_pos two_pos hC₁) (pow_pos (by linarith) _), lt_min hν₀₁ one_pos,
    min_le_right _ _, ?_⟩⟩
  intro ν hν hνle tr htr s hs hsS z hz
  have hν1 : ν ≤ 1 := hνle.trans (min_le_right _ _)
  have hν0 : ν ≤ ν₀₁ := hνle.trans (min_le_left _ _)
  have hSig0 : 0 ≤ Sig / ν := div_nonneg hSig.le hν.le
  have h := hT' (Sig / ν) hSig0 ν hν hν0 tr htr 0 le_rfl s hs hsS z (by rw [add_zero]; exact hz)
  have hv : ‖UnforcedLeray.Short.PartI.ageJet ℓ j tr.v s z‖ ≤
      UnforcedLeray.Short.PartI.polyPS C₁ N₁ ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) (Sig / ν) *
        (Real.exp (-(b * 0 / UnforcedLeray.Short.PartI.trainPeriod 2 ν)) +
          Real.exp (-(b * 0 ^ 2 / (C₀ + ν * (Sig / ν))))) := h.2.1
  have e : Real.exp (-(b * 0 / UnforcedLeray.Short.PartI.trainPeriod 2 ν)) +
      Real.exp (-(b * 0 ^ 2 / (C₀ + ν * (Sig / ν)))) = 2 := by
    norm_num
  rw [e] at hv
  have hc2 : UnforcedLeray.Short.PartI.trainPeriod 2 ν = (ν⁻¹) ^ 2 := by
    rw [velTail_trainPeriod_two hν, inv_pow]
  have hpoly : UnforcedLeray.Short.PartI.polyPS C₁ N₁ ν
      (UnforcedLeray.Short.PartI.trainPeriod 2 ν) (Sig / ν) =
        C₁ * ((1 + (ν⁻¹) ^ 2 + ν⁻¹) * (1 + Sig * ν⁻¹)) ^ N₁ := by
    unfold UnforcedLeray.Short.PartI.polyPS
    rw [hc2, div_eq_mul_inv]
  rw [hpoly] at hv
  have ht : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have key := velTail_poly_bound C₁ Sig ν⁻¹ N₁ hC₁.le hSig.le ht
  have key2 : C₁ * ((1 + (ν⁻¹) ^ 2 + ν⁻¹) * (1 + Sig * ν⁻¹)) ^ N₁ * 2 ≤
      C₁ * (3 * (1 + Sig)) ^ N₁ * (ν⁻¹) ^ (3 * N₁) * 2 :=
    mul_le_mul_of_nonneg_right key (by norm_num)
  rw [← inv_pow]
  refine (hv.trans key2).trans (le_of_eq ?_)
  ring

/-- **Tail region** (SP 463-467, `TrainTransverseTails` with `ρ = 2`), the four jets of `v`
on `0 < s ≤ Σ/ν`, `|η| ≥ C'/ν + 2`. -/
theorem rawVelTailJets_of (hT : UnforcedLeray.Short.PartI.TrainTransverseTails) :
    UnforcedLeray.Short.IIb.RawVelTailJets := by
  obtain ⟨A₁, hA₁, H₁⟩ := velTail_tailJet hT 0 0
  obtain ⟨A₂, hA₂, H₂⟩ := velTail_tailJet hT 1 0
  obtain ⟨A₃, hA₃, H₃⟩ := velTail_tailJet hT 0 1
  obtain ⟨A₄, hA₄, H₄⟩ := velTail_tailJet hT 2 0
  refine ⟨A₁ + A₂ + A₃ + A₄, by linarith, fun Sig hSig dm dp hdm => ?_⟩
  obtain ⟨C₁, N₁, ν₁, hC₁, hν₁, hν₁le, G₁⟩ := H₁ Sig hSig
  obtain ⟨C₂, N₂, ν₂, hC₂, hν₂, hν₂le, G₂⟩ := H₂ Sig hSig
  obtain ⟨C₃, N₃, ν₃, hC₃, hν₃, hν₃le, G₃⟩ := H₃ Sig hSig
  obtain ⟨C₄, N₄, ν₄, hC₄, hν₄, hν₄le, G₄⟩ := H₄ Sig hSig
  refine ⟨C₁ + C₂ + C₃ + C₄, N₁ + N₂ + N₃ + N₄, min (min ν₁ ν₂) (min ν₃ ν₄),
    add_pos (add_pos (add_pos hC₁ hC₂) hC₃) hC₄,
    lt_min (lt_min hν₁ hν₂) (lt_min hν₃ hν₄), ?_⟩
  intro p d hd hν hS x hx0 hxH hη
  have hνp : 0 < p.ν := p.ν_pos
  have hν1 : p.ν ≤ ν₁ := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν2 : p.ν ≤ ν₂ := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν3 : p.ν ≤ ν₃ := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν4 : p.ν ≤ ν₄ := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hνone : p.ν ≤ 1 := hν1.trans hν₁le
  have hsH : x.1 ≤ Sig / p.ν := by
    have : p.H = p.ageCut / p.ν := rfl
    rw [← hS]
    rw [this] at hxH
    exact hxH
  have hA1 : A₁ ≤ A₁ + A₂ + A₃ + A₄ := by linarith
  have hA2 : A₂ ≤ A₁ + A₂ + A₃ + A₄ := by linarith
  have hA3 : A₃ ≤ A₁ + A₂ + A₃ + A₄ := by linarith
  have hA4 : A₄ ≤ A₁ + A₂ + A₃ + A₄ := by linarith
  have hη1 : A₁ / p.ν + 2 ≤ |x.2.2| := by
    linarith [div_le_div_of_nonneg_right hA1 hνp.le]
  have hη2 : A₂ / p.ν + 2 ≤ |x.2.2| := by
    linarith [div_le_div_of_nonneg_right hA2 hνp.le]
  have hη3 : A₃ / p.ν + 2 ≤ |x.2.2| := by
    linarith [div_le_div_of_nonneg_right hA3 hνp.le]
  have hη4 : A₄ / p.ν + 2 ≤ |x.2.2| := by
    linarith [div_le_div_of_nonneg_right hA4 hνp.le]
  obtain ⟨tr', hbuc, hv⟩ :=
    velTail_transport (hd.c_eq.trans (velTail_trainPeriod_two hνp).symm) p.train hd.train_buc
  have g₁ := G₁ p.ν hνp hν1 tr' hbuc x.1 hx0 hsH x.2 hη1
  have g₂ := G₂ p.ν hνp hν2 tr' hbuc x.1 hx0 hsH x.2 hη2
  have g₃ := G₃ p.ν hνp hν3 tr' hbuc x.1 hx0 hsH x.2 hη3
  have g₄ := G₄ p.ν hνp hν4 tr' hbuc x.1 hx0 hsH x.2 hη4
  rw [hv] at g₁ g₂ g₃ g₄
  have k₁ : C₁ * (p.ν ^ N₁)⁻¹ ≤ C₁ * (p.ν ^ (N₁ + N₂ + N₃ + N₄))⁻¹ :=
    mul_le_mul_of_nonneg_left (velTail_inv_pow_mono hνp hνone (by omega)) hC₁.le
  have k₂ : C₂ * (p.ν ^ N₂)⁻¹ ≤ C₂ * (p.ν ^ (N₁ + N₂ + N₃ + N₄))⁻¹ :=
    mul_le_mul_of_nonneg_left (velTail_inv_pow_mono hνp hνone (by omega)) hC₂.le
  have k₃ : C₃ * (p.ν ^ N₃)⁻¹ ≤ C₃ * (p.ν ^ (N₁ + N₂ + N₃ + N₄))⁻¹ :=
    mul_le_mul_of_nonneg_left (velTail_inv_pow_mono hνp hνone (by omega)) hC₃.le
  have k₄ : C₄ * (p.ν ^ N₄)⁻¹ ≤ C₄ * (p.ν ^ (N₁ + N₂ + N₃ + N₄))⁻¹ :=
    mul_le_mul_of_nonneg_left (velTail_inv_pow_mono hνp hνone (by omega)) hC₄.le
  linarith [g₁, g₂, g₃, g₄, k₁, k₂, k₃, k₄]

end UnforcedLeray.Short.IIb

end
