import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T18_3_1_4
import UnforcedLeray.Short.PartIIIa.Sub.Audit0.AuditT18_3_1_4_GainFactsCorrected

/-!
# Part III-a, `PartIII-a:T18/3/1/4/2`: `CoreToSmoothWeighted` (Lemma 2)

Source of record: `the November 2 reference manuscript`, lines 3541-3552 and 3427-3440.

Route: `CoreIdentity` with the smooth weight `w = ψ s^{-1/2} q`, `q = (gainG γ ν)^{-2}`. Then
`w' = q (ψ' s^{-1/2} - ½ ψ s^{-3/2} - 2 h ψ s^{-1/2})` with `h = γ/(1+νs)²`, the conjugated
energies are `q` times the unconjugated ones, the cross term is bounded a.e. in `s` by Cauchy-Schwarz
on the cell, and the term `2 h ψ s^{-1/2} E_u ≥ 0` is dropped.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.CoreToSmoothAux

/-- The gain weight `q(s) = (gainG γ ν s)⁻¹ ^ 2`. -/
def qWt (γ ν s : ℝ) : ℝ := (gainG γ ν s)⁻¹ ^ 2

/-- `H(s) = s^{-1/2} q(s)`. -/
def Hwt (γ ν s : ℝ) : ℝ := s ^ (-1 / 2 : ℝ) * qWt γ ν s

/-- The weight `w(s) = ψ(s) H(s)`. -/
def wWeight (γ ν : ℝ) (ψ : ℝ → ℝ) (s : ℝ) : ℝ := ψ s * Hwt γ ν s

theorem exists_Icc_contains (T : Set ℝ) (hT : IsCompact T) (hpos : T ⊆ Ioi 0) :
    ∃ s1 s2 : ℝ, 0 < s1 ∧ s1 < s2 ∧ T ⊆ Icc s1 s2 := by
  have hU : IsCompact (T ∪ {1}) := hT.union isCompact_singleton
  have hUne : (T ∪ {1}).Nonempty := ⟨1, Or.inr rfl⟩
  obtain ⟨m, hmU, hmin⟩ := hU.exists_isMinOn hUne continuousOn_id
  obtain ⟨M, hMU, hmax⟩ := hU.exists_isMaxOn hUne continuousOn_id
  rw [isMinOn_iff] at hmin
  rw [isMaxOn_iff] at hmax
  have hm0 : 0 < m := by
    rcases hmU with h | h
    · exact hpos h
    · rw [Set.mem_singleton_iff.1 h]; norm_num
  have h1 : m ≤ 1 := hmin 1 (Or.inr rfl)
  have h2 : (1 : ℝ) ≤ M := hmax 1 (Or.inr rfl)
  refine ⟨m, M + 1, hm0, by linarith, fun t ht => ⟨?_, ?_⟩⟩
  · have : m ≤ t := hmin t (Or.inl ht)
    exact this
  · have : t ≤ M := hmax t (Or.inl ht)
    linarith

theorem hasDerivAt_qWt (γ ν : ℝ) {s : ℝ} (hν : 0 < ν) (hs : 0 < s) :
    HasDerivAt (qWt γ ν) (-2 * (γ / (1 + ν * s) ^ 2) * qWt γ ν s) s := by
  have hpos1 : 0 < 1 + ν * s := by have := mul_pos hν hs; linarith
  have hg := hasDerivAt_gainG γ ν hpos1.ne'
  have hi := hg.inv (gainG_pos γ ν s).ne'
  have hp := hi.pow 2
  unfold qWt
  refine HasDerivAt.congr_deriv hp ?_
  have hgp := (gainG_pos γ ν s).ne'
  rw [show (2 - 1 : ℕ) = 1 from rfl, pow_one]
  (try simp only [Pi.inv_apply, Pi.pow_apply])
  push_cast
  first | (field_simp; ring) | field_simp

theorem hasDerivAt_Hwt (γ ν : ℝ) {s : ℝ} (hν : 0 < ν) (hs : 0 < s) :
    HasDerivAt (Hwt γ ν)
      ((-1 / 2) * (s ^ (-1 / 2 : ℝ) / s) * qWt γ ν s +
        s ^ (-1 / 2 : ℝ) * (-2 * (γ / (1 + ν * s) ^ 2) * qWt γ ν s)) s := by
  have h1 := Real.hasDerivAt_rpow_const (x := s) (p := (-1 / 2 : ℝ)) (Or.inl hs.ne')
  have h2 := hasDerivAt_qWt γ ν hν hs
  have h3 := h1.mul h2
  rw [Real.rpow_sub_one hs.ne'] at h3
  exact h3

theorem deriv_wWeight (γ ν : ℝ) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) {s : ℝ} (hν : 0 < ν)
    (hs : 0 < s) :
    deriv (wWeight γ ν ψ) s = deriv ψ s * Hwt γ ν s +
      ψ s * ((-1 / 2) * (s ^ (-1 / 2 : ℝ) / s) * qWt γ ν s +
        s ^ (-1 / 2 : ℝ) * (-2 * (γ / (1 + ν * s) ^ 2) * qWt γ ν s)) := by
  have hd1 : DifferentiableAt ℝ ψ s := (hψ.differentiable (by simp)).differentiableAt
  have hd2 : DifferentiableAt ℝ (Hwt γ ν) s := (hasDerivAt_Hwt γ ν hν hs).differentiableAt
  have hw : wWeight γ ν ψ = ψ * Hwt γ ν := rfl
  rw [hw, deriv_mul hd1 hd2, (hasDerivAt_Hwt γ ν hν hs).deriv]

theorem contDiff_wWeight (γ ν : ℝ) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hν : 0 < ν)
    (hsupp : tsupport ψ ⊆ Ioi 0) : ContDiff ℝ ∞ (wWeight γ ν ψ) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  by_cases hs : s ∈ tsupport ψ
  · have hpos : 0 < s := hsupp hs
    have hpos1 : 0 < 1 + ν * s := by have := mul_pos hν hpos; linarith
    have hnum : ContDiffAt ℝ ∞ (fun x : ℝ => γ * x) s := by fun_prop
    have hden : ContDiffAt ℝ ∞ (fun x : ℝ => 1 + ν * x) s := by fun_prop
    have hg : ContDiffAt ℝ ∞ (gainG γ ν) s := by
      unfold gainG
      exact (hnum.div hden hpos1.ne').exp
    have hq : ContDiffAt ℝ ∞ (qWt γ ν) s := by
      unfold qWt
      exact (hg.inv (gainG_pos γ ν s).ne').pow 2
    have hA : ContDiffAt ℝ ∞ (fun y : ℝ => y ^ (-1 / 2 : ℝ)) s :=
      Real.contDiffAt_rpow_const_of_ne hpos.ne'
    have hH : ContDiffAt ℝ ∞ (Hwt γ ν) s := by
      unfold Hwt
      exact hA.mul hq
    exact (hψ.contDiffAt).mul hH
  · have h0 : ψ =ᶠ[𝓝 s] 0 := notMem_tsupport_iff_eventuallyEq.1 hs
    have h1 : wWeight γ ν ψ =ᶠ[𝓝 s] 0 := by
      filter_upwards [h0] with t ht
      simp [wWeight, ht]
    exact contDiffAt_const.congr_of_eventuallyEq h1

theorem tsupport_wWeight_subset (γ ν : ℝ) (ψ : ℝ → ℝ) :
    tsupport (wWeight γ ν ψ) ⊆ tsupport ψ := by
  have h := tsupport_mul_subset_left (f := ψ) (g := Hwt γ ν)
  exact h

theorem hasCompactSupport_wWeight (γ ν : ℝ) (ψ : ℝ → ℝ) (hψc : HasCompactSupport ψ) :
    HasCompactSupport (wWeight γ ν ψ) := by
  have h := hψc.mul_right (f' := Hwt γ ν)
  exact h

theorem intK_mul {K : Set ℝ} (hK : IsCompact K) {X c : ℝ → ℝ} (hX : IntegrableOn X K)
    (hc : ContinuousOn c K) : IntegrableOn (fun s => c s * X s) K := by
  have h := hX.mul_continuousOn hc hK
  exact h.congr_fun (fun s _ => mul_comm _ _) hK.measurableSet

/-- The real-analysis core: the weighted inequality for the integrand functions `E, N, R, J` on
`[s₁,s₂]`, from the identity of `CoreIdentity` for the weight `wWeight γ ν ψ`. -/
theorem real_core (γ ν μr s1 s2 : ℝ) (hν : 0 < ν) (hγ : 0 ≤ γ) (hs1 : 0 < s1) (hs12 : s1 < s2)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψsupp : tsupport ψ ⊆ Icc s1 s2) (hψnn : ∀ s, 0 ≤ ψ s)
    (E N R J : ℝ → ℝ)
    (hE : IntegrableOn E (Icc s1 s2)) (hN : IntegrableOn N (Icc s1 s2))
    (hR : IntegrableOn R (Icc s1 s2)) (hJ : IntegrableOn J (Icc s1 s2))
    (hE0 : ∀ s, 0 ≤ E s)
    (hRJ : ∀ᵐ s ∂(volume.restrict (Icc s1 s2)), 0 ≤ R s + J s)
    (hcore : ∫ s in Ioi (0 : ℝ), deriv (wWeight γ ν ψ) s * E s =
      ∫ s in Ioi (0 : ℝ), wWeight γ ν ψ s * (2 * μr / s * E s + 2 * ν * N s + 2 * R s)) :
    ∫ s in Ioi (0 : ℝ), ψ s * ((1 / 2 + 2 * μr) * s ^ (-3 / 2 : ℝ) * (qWt γ ν s * E s) +
        2 * ν * s ^ (-1 / 2 : ℝ) * (qWt γ ν s * N s))
      ≤ (∫ s in Ioi (0 : ℝ), deriv ψ s * (s ^ (-1 / 2 : ℝ) * (qWt γ ν s * E s))) +
        2 * ∫ s in Ioi (0 : ℝ), ψ s * s ^ (-1 / 2 : ℝ) * (qWt γ ν s * J s) := by
  have hKc : IsCompact (Icc s1 s2) := isCompact_Icc
  have hKm : MeasurableSet (Icc s1 s2) := measurableSet_Icc
  have hpos : ∀ s ∈ Icc s1 s2, 0 < s := fun s hs => lt_of_lt_of_le hs1 hs.1
  have hsub : Icc s1 s2 ⊆ Ioi (0 : ℝ) := fun s hs => hpos s hs
  have hsupp' : tsupport ψ ⊆ Ioi (0 : ℝ) := hψsupp.trans hsub
  -- vanishing outside the compact interval
  have hψ0 : ∀ s, s ∉ Icc s1 s2 → ψ s = 0 := fun s hs =>
    image_eq_zero_of_notMem_tsupport (fun h => hs (hψsupp h))
  have hψd0 : ∀ s, s ∉ Icc s1 s2 → deriv ψ s = 0 := fun s hs =>
    deriv_of_notMem_tsupport (fun h => hs (hψsupp h))
  have hwd0 : ∀ s, s ∉ Icc s1 s2 → deriv (wWeight γ ν ψ) s = 0 := fun s hs =>
    deriv_of_notMem_tsupport (fun h => hs (hψsupp (tsupport_wWeight_subset γ ν ψ h)))
  have hw0 : ∀ s, s ∉ Icc s1 s2 → wWeight γ ν ψ s = 0 := fun s hs => by
    simp [wWeight, hψ0 s hs]
  have toK : ∀ f : ℝ → ℝ, (∀ s, s ∉ Icc s1 s2 → f s = 0) →
      ∫ s in Ioi (0 : ℝ), f s = ∫ s in Icc s1 s2, f s := fun f hf =>
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub
      (fun s hs => hf s hs.2)
  -- powers
  have hpow : ∀ s : ℝ, 0 < s → s ^ (-3 / 2 : ℝ) = s ^ (-1 / 2 : ℝ) / s := by
    intro s hs
    rw [show (-3 / 2 : ℝ) = -1 / 2 - 1 by norm_num, Real.rpow_sub_one hs.ne']
  -- continuity
  have hcψ : Continuous ψ := hψ.continuous
  have hcψ' : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
  have hcA : ContinuousOn (fun s : ℝ => s ^ (-1 / 2 : ℝ)) (Icc s1 s2) := fun s hs =>
    (Real.continuousAt_rpow_const s _ (Or.inl (hpos s hs).ne')).continuousWithinAt
  have hcA3 : ContinuousOn (fun s : ℝ => s ^ (-3 / 2 : ℝ)) (Icc s1 s2) := fun s hs =>
    (Real.continuousAt_rpow_const s _ (Or.inl (hpos s hs).ne')).continuousWithinAt
  have hcq : ContinuousOn (qWt γ ν) (Icc s1 s2) := fun s hs =>
    (hasDerivAt_qWt γ ν hν (hpos s hs)).continuousAt.continuousWithinAt
  have hdw : Continuous (deriv (wWeight γ ν ψ)) :=
    (contDiff_wWeight γ ν ψ hψ hν hsupp').continuous_deriv (by simp)
  have hcw : Continuous (wWeight γ ν ψ) := (contDiff_wWeight γ ν ψ hψ hν hsupp').continuous
  have hcμ : ContinuousOn (fun s : ℝ => 2 * μr / s) (Icc s1 s2) :=
    continuousOn_const.div continuousOn_id (fun s hs => (hpos s hs).ne')
  have hcR : ContinuousOn (fun s : ℝ => γ / (1 + ν * s) ^ 2) (Icc s1 s2) := by
    intro s hs
    apply ContinuousAt.continuousWithinAt
    have hpos1 : 0 < 1 + ν * s := by have := mul_pos hν (hpos s hs); linarith
    have hc2 : ContinuousAt (fun t : ℝ => (1 + ν * t) ^ 2) s := by fun_prop
    exact continuousAt_const.div hc2 (pow_ne_zero 2 hpos1.ne')
  -- nonnegativity on the interval
  have hqWt0 : ∀ s, 0 ≤ qWt γ ν s := fun s => by unfold qWt; exact sq_nonneg _
  have hA0 : ∀ s : ℝ, 0 < s → 0 ≤ s ^ (-1 / 2 : ℝ) := fun s hs => Real.rpow_nonneg hs.le _
  have hcP0 : ∀ s ∈ Icc s1 s2,
      0 ≤ ψ s * s ^ (-1 / 2 : ℝ) * (γ / (1 + ν * s) ^ 2) * qWt γ ν s := fun s hs =>
    mul_nonneg (mul_nonneg (mul_nonneg (hψnn s) (hA0 s (hpos s hs)))
      (div_nonneg hγ (sq_nonneg _))) (hqWt0 s)
  have hcQ0 : ∀ s ∈ Icc s1 s2, 0 ≤ ψ s * s ^ (-1 / 2 : ℝ) * qWt γ ν s := fun s hs =>
    mul_nonneg (mul_nonneg (hψnn s) (hA0 s (hpos s hs))) (hqWt0 s)
  -- integrability of the pieces on the interval
  have hI1 : IntegrableOn (fun s => deriv (wWeight γ ν ψ) s * E s) (Icc s1 s2) :=
    intK_mul hKc hE hdw.continuousOn
  have hI2 : IntegrableOn
      (fun s => wWeight γ ν ψ s * (2 * μr / s * E s + 2 * ν * N s + 2 * R s)) (Icc s1 s2) := by
    have a1 : IntegrableOn (fun s => (wWeight γ ν ψ s * (2 * μr / s)) * E s) (Icc s1 s2) :=
      intK_mul hKc hE (hcw.continuousOn.mul hcμ)
    have a2 : IntegrableOn (fun s => (wWeight γ ν ψ s * (2 * ν)) * N s) (Icc s1 s2) :=
      intK_mul hKc hN (hcw.continuousOn.mul continuousOn_const)
    have a3 : IntegrableOn (fun s => (wWeight γ ν ψ s * 2) * R s) (Icc s1 s2) :=
      intK_mul hKc hR (hcw.continuousOn.mul continuousOn_const)
    refine ((a1.add a2).add a3).congr_fun (fun s _ => ?_) hKm
    (try simp only [Pi.mul_apply, Pi.add_apply])
    ring
  have hI5 : IntegrableOn (fun s => deriv ψ s * (s ^ (-1 / 2 : ℝ) * (qWt γ ν s * E s)))
      (Icc s1 s2) :=
    (intK_mul hKc hE (hcψ'.continuousOn.mul (hcA.mul hcq))).congr_fun
      (fun s _ => by (try simp only [Pi.mul_apply, Pi.add_apply]); ring) hKm
  have hI6 : IntegrableOn (fun s => ψ s * s ^ (-1 / 2 : ℝ) * (qWt γ ν s * J s)) (Icc s1 s2) :=
    (intK_mul hKc hJ ((hcψ.continuousOn.mul hcA).mul hcq)).congr_fun
      (fun s _ => by (try simp only [Pi.mul_apply, Pi.add_apply]); ring) hKm
  have hc7E : ContinuousOn (fun s : ℝ => ψ s * ((1 / 2 + 2 * μr) * s ^ (-3 / 2 : ℝ) * qWt γ ν s))
      (Icc s1 s2) :=
    hcψ.continuousOn.mul (((continuousOn_const (c := 1 / 2 + 2 * μr)).mul hcA3).mul hcq)
  have hc7N : ContinuousOn (fun s : ℝ => ψ s * (2 * ν * s ^ (-1 / 2 : ℝ) * qWt γ ν s))
      (Icc s1 s2) :=
    hcψ.continuousOn.mul (((continuousOn_const (c := 2 * ν)).mul hcA).mul hcq)
  have hI7 : IntegrableOn (fun s => ψ s * ((1 / 2 + 2 * μr) * s ^ (-3 / 2 : ℝ) *
      (qWt γ ν s * E s) + 2 * ν * s ^ (-1 / 2 : ℝ) * (qWt γ ν s * N s))) (Icc s1 s2) :=
    ((intK_mul hKc hE hc7E).add (intK_mul hKc hN hc7N)).congr_fun
      (fun s _ => by (try simp only [Pi.mul_apply, Pi.add_apply]); ring) hKm
  have hP : IntegrableOn (fun s => (ψ s * s ^ (-1 / 2 : ℝ) * (γ / (1 + ν * s) ^ 2) *
      qWt γ ν s) * E s) (Icc s1 s2) :=
    intK_mul hKc hE (((hcψ.continuousOn.mul hcA).mul hcR).mul hcq)
  have hQ : IntegrableOn (fun s => (ψ s * s ^ (-1 / 2 : ℝ) * qWt γ ν s) * (R s + J s))
      (Icc s1 s2) :=
    intK_mul hKc (hR.add hJ) ((hcψ.continuousOn.mul hcA).mul hcq)
  -- vanishing outside
  have hz1 : ∀ s, s ∉ Icc s1 s2 → deriv (wWeight γ ν ψ) s * E s = 0 := fun s hs => by
    rw [hwd0 s hs, zero_mul]
  have hz2 : ∀ s, s ∉ Icc s1 s2 →
      wWeight γ ν ψ s * (2 * μr / s * E s + 2 * ν * N s + 2 * R s) = 0 := fun s hs => by
    rw [hw0 s hs, zero_mul]
  have hz5 : ∀ s, s ∉ Icc s1 s2 → deriv ψ s * (s ^ (-1 / 2 : ℝ) * (qWt γ ν s * E s)) = 0 :=
    fun s hs => by rw [hψd0 s hs, zero_mul]
  have hz6 : ∀ s, s ∉ Icc s1 s2 → ψ s * s ^ (-1 / 2 : ℝ) * (qWt γ ν s * J s) = 0 :=
    fun s hs => by simp [hψ0 s hs]
  have hz7 : ∀ s, s ∉ Icc s1 s2 → ψ s * ((1 / 2 + 2 * μr) * s ^ (-3 / 2 : ℝ) *
      (qWt γ ν s * E s) + 2 * ν * s ^ (-1 / 2 : ℝ) * (qWt γ ν s * N s)) = 0 :=
    fun s hs => by simp [hψ0 s hs]
  -- the core identity on the interval
  have hcoreK : ∫ s in Icc s1 s2, deriv (wWeight γ ν ψ) s * E s =
      ∫ s in Icc s1 s2, wWeight γ ν ψ s * (2 * μr / s * E s + 2 * ν * N s + 2 * R s) := by
    rw [← toK _ hz1, ← toK _ hz2]
    exact hcore
  have hres : ∫ s in Icc s1 s2, (deriv (wWeight γ ν ψ) s * E s -
      wWeight γ ν ψ s * (2 * μr / s * E s + 2 * ν * N s + 2 * R s)) = 0 := by
    rw [integral_sub hI1 hI2]
    exact sub_eq_zero.2 hcoreK
  -- pointwise algebra on the interval
  have hpt : ∀ s ∈ Icc s1 s2,
      (deriv ψ s * (s ^ (-1 / 2 : ℝ) * (qWt γ ν s * E s)) +
        2 * (ψ s * s ^ (-1 / 2 : ℝ) * (qWt γ ν s * J s)) -
        ψ s * ((1 / 2 + 2 * μr) * s ^ (-3 / 2 : ℝ) * (qWt γ ν s * E s) +
          2 * ν * s ^ (-1 / 2 : ℝ) * (qWt γ ν s * N s))) =
      ((deriv (wWeight γ ν ψ) s * E s -
          wWeight γ ν ψ s * (2 * μr / s * E s + 2 * ν * N s + 2 * R s)) +
        2 * ((ψ s * s ^ (-1 / 2 : ℝ) * (γ / (1 + ν * s) ^ 2) * qWt γ ν s) * E s) +
        2 * ((ψ s * s ^ (-1 / 2 : ℝ) * qWt γ ν s) * (R s + J s))) := by
    intro s hs
    have hs0 := hpos s hs
    rw [deriv_wWeight γ ν ψ hψ hν hs0, hpow s hs0]
    simp only [wWeight, Hwt]
    ring
  have hsplit := setIntegral_congr_fun (μ := volume) hKm hpt
  -- the integrals of the pieces
  have hPnn : 0 ≤ ∫ s in Icc s1 s2, (ψ s * s ^ (-1 / 2 : ℝ) * (γ / (1 + ν * s) ^ 2) *
      qWt γ ν s) * E s :=
    setIntegral_nonneg hKm (fun s hs => mul_nonneg (hcP0 s hs) (hE0 s))
  have hQnn : 0 ≤ ∫ s in Icc s1 s2, (ψ s * s ^ (-1 / 2 : ℝ) * qWt γ ν s) * (R s + J s) := by
    apply setIntegral_nonneg_ae hKm
    have hae := (ae_restrict_iff' hKm).1 hRJ
    filter_upwards [hae] with x hx hxK
    exact mul_nonneg (hcQ0 x hxK) (hx hxK)
  have hA56 : IntegrableOn (fun s => deriv ψ s * (s ^ (-1 / 2 : ℝ) * (qWt γ ν s * E s)) +
      2 * (ψ s * s ^ (-1 / 2 : ℝ) * (qWt γ ν s * J s))) (Icc s1 s2) :=
    hI5.add (hI6.const_mul 2)
  have hR1 : IntegrableOn (fun s => deriv (wWeight γ ν ψ) s * E s -
      wWeight γ ν ψ s * (2 * μr / s * E s + 2 * ν * N s + 2 * R s)) (Icc s1 s2) :=
    hI1.sub hI2
  have hR2 : IntegrableOn (fun s => (deriv (wWeight γ ν ψ) s * E s -
      wWeight γ ν ψ s * (2 * μr / s * E s + 2 * ν * N s + 2 * R s)) +
      2 * ((ψ s * s ^ (-1 / 2 : ℝ) * (γ / (1 + ν * s) ^ 2) * qWt γ ν s) * E s)) (Icc s1 s2) :=
    hR1.add (hP.const_mul 2)
  have e1 : ∫ s in Icc s1 s2, (deriv ψ s * (s ^ (-1 / 2 : ℝ) * (qWt γ ν s * E s)) +
        2 * (ψ s * s ^ (-1 / 2 : ℝ) * (qWt γ ν s * J s)) -
        ψ s * ((1 / 2 + 2 * μr) * s ^ (-3 / 2 : ℝ) * (qWt γ ν s * E s) +
          2 * ν * s ^ (-1 / 2 : ℝ) * (qWt γ ν s * N s))) =
      (∫ s in Icc s1 s2, deriv ψ s * (s ^ (-1 / 2 : ℝ) * (qWt γ ν s * E s))) +
        2 * (∫ s in Icc s1 s2, ψ s * s ^ (-1 / 2 : ℝ) * (qWt γ ν s * J s)) -
        ∫ s in Icc s1 s2, ψ s * ((1 / 2 + 2 * μr) * s ^ (-3 / 2 : ℝ) * (qWt γ ν s * E s) +
          2 * ν * s ^ (-1 / 2 : ℝ) * (qWt γ ν s * N s)) := by
    rw [integral_sub hA56 hI7, integral_add hI5 (hI6.const_mul 2), integral_const_mul]
  have e2 : ∫ s in Icc s1 s2, ((deriv (wWeight γ ν ψ) s * E s -
          wWeight γ ν ψ s * (2 * μr / s * E s + 2 * ν * N s + 2 * R s)) +
        2 * ((ψ s * s ^ (-1 / 2 : ℝ) * (γ / (1 + ν * s) ^ 2) * qWt γ ν s) * E s) +
        2 * ((ψ s * s ^ (-1 / 2 : ℝ) * qWt γ ν s) * (R s + J s))) =
      (∫ s in Icc s1 s2, (deriv (wWeight γ ν ψ) s * E s -
          wWeight γ ν ψ s * (2 * μr / s * E s + 2 * ν * N s + 2 * R s))) +
        2 * (∫ s in Icc s1 s2, (ψ s * s ^ (-1 / 2 : ℝ) * (γ / (1 + ν * s) ^ 2) * qWt γ ν s) * E s) +
        2 * (∫ s in Icc s1 s2, (ψ s * s ^ (-1 / 2 : ℝ) * qWt γ ν s) * (R s + J s)) := by
    rw [integral_add hR2 (hQ.const_mul 2), integral_add hR1 (hP.const_mul 2),
      integral_const_mul, integral_const_mul]
  -- the goal, moved to the interval
  rw [toK _ hz7, toK _ hz5, toK _ hz6]
  linarith [e1, hsplit, e2, hres, hPnn, hQnn]

end UnforcedLeray.Short.IIIa.CoreToSmoothAux

namespace UnforcedLeray.Short.IIIa.CoreToSmoothAux

theorem ct_measurable_vnorm2 {α : Type*} [MeasurableSpace α] {f : α → Fin 2 → ℂ}
    (hf : ∀ i, Measurable fun a => f a i) : Measurable fun a => vnorm2 (f a) := by
  unfold vnorm2
  apply Measurable.sqrt
  apply Finset.measurable_sum
  intro i _
  exact ((hf i).norm).pow_const 2

theorem ct_measurable_tnorm2 {α : Type*} [MeasurableSpace α] {f : α → Fin 2 → Fin 2 → ℂ}
    (hf : ∀ i j, Measurable fun a => f a i j) : Measurable fun a => tnorm2 (f a) := by
  unfold tnorm2
  apply Measurable.sqrt
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  exact ((hf i j).norm).pow_const 2

theorem ct_abs_mul_le (x y : ℝ) : |x * y| ≤ x ^ 2 + y ^ 2 := by
  rw [abs_mul]
  nlinarith [abs_nonneg x, abs_nonneg y, sq_abs x, sq_abs y, sq_nonneg (|x| - |y|)]

theorem ct_integrable_of_bound {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : Measurable f) (hbd : ∀ p, |f p| ≤ g p) (hfin : ∫⁻ p, ENNReal.ofReal (g p) ∂μ < ⊤) :
    Integrable f μ := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  refine lt_of_le_of_lt (lintegral_mono fun p => ?_) hfin
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal (hbd p)

theorem ct_ae_slice {s1 s2 c : ℝ} {f g : ℝ × (ℝ × ℝ) → ℝ} (hf : Measurable f)
    (hbd : ∀ p, |f p| ≤ g p) (hfin : ∫⁻ p in Icc s1 s2 ×ˢ B0579.cell c, ENNReal.ofReal (g p) < ⊤) :
    ∀ᵐ s ∂(volume.restrict (Icc s1 s2)),
      Integrable (fun x => f (s, x)) (volume.restrict (B0579.cell c)) := by
  have hI : Integrable f ((volume.restrict (Icc s1 s2)).prod (volume.restrict (B0579.cell c))) := by
    rw [Measure.prod_restrict]
    exact ct_integrable_of_bound hf hbd hfin
  exact hI.prod_right_ae

theorem ct_tnorm2_gainConj_eq (γ ν : ℝ) (T : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (p : ℝ × (ℝ × ℝ)) :
    tnorm2 (gainConj γ ν T p) = (gainG γ ν p.1)⁻¹ * tnorm2 (T p) := by
  unfold gainConj
  rw [tnorm2_smul_real, abs_of_pos (inv_pos.2 (gainG_pos γ ν p.1))]

end UnforcedLeray.Short.IIIa.CoreToSmoothAux

open UnforcedLeray.Short.IIIa UnforcedLeray.Short.IIIa.CoreToSmoothAux

/-- **Lemma 2** (`PartIII-a:T18/3/1/4/2`; SP 3541-3552): `CoreAll` and `EnergyLocIntegrable` give the
weighted inequality for smooth cutoffs. -/
theorem coreToSmoothWeighted : UnforcedLeray.Short.IIIa.CoreToSmoothWeighted := by
  unfold UnforcedLeray.Short.IIIa.CoreToSmoothWeighted
    UnforcedLeray.Short.IIIa.WeightedEnergyIdentitySmooth
  intro hCore hLoc c ν γ μ hc hν hγ F b G hF hmeasF hcaus ψ hψ hψc hψsupp hψnn
  obtain ⟨s1, s2, hs1, hs12, hsub⟩ :=
    exists_Icc_contains (tsupport ψ) (hψc : IsCompact (tsupport ψ)) hψsupp
  have hD : FreeSolData c ν μ F b G := ⟨hc, hν, hF, hmeasF, hcaus⟩
  obtain ⟨hEI, hNI, hRI, hJI⟩ := hLoc c ν μ F b G hD s1 s2 hs1 hs12
  have hcore := hCore c ν μ F b G hD (wWeight γ ν ψ) (contDiff_wWeight γ ν ψ hψ hν hψsupp)
    (hasCompactSupport_wWeight γ ν ψ hψc) ((tsupport_wWeight_subset γ ν ψ).trans hψsupp)
  have hE0 : ∀ s, 0 ≤ energyE c b s := fun s => integral_nonneg fun x => sq_nonneg _
  have hgm : ∀ i j, Measurable fun p => G p i j := hcaus.gradMeasurable
  have hMfin : ∫⁻ p in Icc s1 s2 ×ˢ UnforcedLeray.B0579.cell c,
      ENNReal.ofReal (tnorm2 (F p) ^ 2 + (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2)) < ⊤ := by
    have hm1 : Measurable fun p => tnorm2 (F p) ^ 2 :=
      (ct_measurable_tnorm2 hmeasF).pow_const 2
    refine lt_of_le_of_lt (lintegral_mono fun p => ENNReal.ofReal_add_le) ?_
    rw [lintegral_add_left hm1.ennreal_ofReal]
    exact ENNReal.add_lt_top.2 ⟨hF s1 s2 hs1 hs12, hcaus.energyLoc s1 s2 hs1 hs12⟩
  have hmeasR : Measurable fun p : ℝ × (ℝ × ℝ) => ∑ i : Fin 2, ∑ j : Fin 2,
      ((F p i j).re * (G p i j).re + (F p i j).im * (G p i j).im) := by
    apply Finset.measurable_sum
    intro i _
    apply Finset.measurable_sum
    intro j _
    exact ((Complex.measurable_re.comp (hmeasF i j)).mul
      (Complex.measurable_re.comp (hgm i j))).add
      ((Complex.measurable_im.comp (hmeasF i j)).mul (Complex.measurable_im.comp (hgm i j)))
  have hmeasT : Measurable fun p : ℝ × (ℝ × ℝ) => tnorm2 (F p) * tnorm2 (G p) :=
    (ct_measurable_tnorm2 hmeasF).mul (ct_measurable_tnorm2 hgm)
  have hbdR : ∀ p : ℝ × (ℝ × ℝ), |∑ i : Fin 2, ∑ j : Fin 2,
      ((F p i j).re * (G p i j).re + (F p i j).im * (G p i j).im)| ≤
      tnorm2 (F p) ^ 2 + (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) := fun p => by
    have h1 := abs_sum_re_le_tnorm2_mul (F p) (G p)
    have h2 := ct_abs_mul_le (tnorm2 (F p)) (tnorm2 (G p))
    have h3 : 0 ≤ vnorm2 (b p) ^ 2 := sq_nonneg _
    have h4 := le_abs_self (tnorm2 (F p) * tnorm2 (G p))
    linarith
  have hbdT : ∀ p : ℝ × (ℝ × ℝ), |tnorm2 (F p) * tnorm2 (G p)| ≤
      tnorm2 (F p) ^ 2 + (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) := fun p => by
    have h2 := ct_abs_mul_le (tnorm2 (F p)) (tnorm2 (G p))
    have h3 : 0 ≤ vnorm2 (b p) ^ 2 := sq_nonneg _
    linarith
  have hsR := ct_ae_slice hmeasR hbdR hMfin
  have hsT := ct_ae_slice hmeasT hbdT hMfin
  have hRJ : ∀ᵐ s ∂(volume.restrict (Icc s1 s2)), 0 ≤ energyR c F G s +
      (fun s => ∫ x in UnforcedLeray.B0579.cell c, tnorm2 (F (s, x)) * tnorm2 (G (s, x))) s := by
    filter_upwards [hsR, hsT] with s hR hT
    have hadd : (∫ x in UnforcedLeray.B0579.cell c, (∑ i : Fin 2, ∑ j : Fin 2,
        ((F (s, x) i j).re * (G (s, x) i j).re + (F (s, x) i j).im * (G (s, x) i j).im) +
        tnorm2 (F (s, x)) * tnorm2 (G (s, x)))) =
        (∫ x in UnforcedLeray.B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2,
          ((F (s, x) i j).re * (G (s, x) i j).re + (F (s, x) i j).im * (G (s, x) i j).im)) +
        ∫ x in UnforcedLeray.B0579.cell c, tnorm2 (F (s, x)) * tnorm2 (G (s, x)) :=
      integral_add hR hT
    have hnn : 0 ≤ ∫ x in UnforcedLeray.B0579.cell c, (∑ i : Fin 2, ∑ j : Fin 2,
        ((F (s, x) i j).re * (G (s, x) i j).re + (F (s, x) i j).im * (G (s, x) i j).im) +
        tnorm2 (F (s, x)) * tnorm2 (G (s, x))) := by
      apply integral_nonneg
      intro x
      have h1 := abs_sum_re_le_tnorm2_mul (F (s, x)) (G (s, x))
      have h2 := neg_abs_le (∑ i : Fin 2, ∑ j : Fin 2,
        ((F (s, x) i j).re * (G (s, x) i j).re + (F (s, x) i j).im * (G (s, x) i j).im))
      show 0 ≤ _
      linarith
    show 0 ≤ (∫ x in UnforcedLeray.B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2,
          ((F (s, x) i j).re * (G (s, x) i j).re + (F (s, x) i j).im * (G (s, x) i j).im)) +
        ∫ x in UnforcedLeray.B0579.cell c, tnorm2 (F (s, x)) * tnorm2 (G (s, x))
    linarith
  have hEu : ∀ s : ℝ, (∫ x in UnforcedLeray.B0579.cell c, vnorm2 (gainConj γ ν b (s, x)) ^ 2) =
      qWt γ ν s * energyE c b s := by
    intro s
    unfold energyE
    rw [← integral_const_mul]
    congr 1
    funext x
    exact vnorm2_gainConj_sq γ ν b (s, x)
  have hNu : ∀ s : ℝ, (∫ x in UnforcedLeray.B0579.cell c, tnorm2 (gainConj γ ν G (s, x)) ^ 2) =
      qWt γ ν s * energyN c G s := by
    intro s
    unfold energyN
    rw [← integral_const_mul]
    congr 1
    funext x
    exact tnorm2_gainConj_sq γ ν G (s, x)
  have hJu : ∀ s : ℝ, (∫ x in UnforcedLeray.B0579.cell c, tnorm2 (gainConj γ ν F (s, x)) *
      tnorm2 (gainConj γ ν G (s, x))) =
      qWt γ ν s * ∫ x in UnforcedLeray.B0579.cell c, tnorm2 (F (s, x)) * tnorm2 (G (s, x)) := by
    intro s
    rw [← integral_const_mul]
    congr 1
    funext x
    rw [ct_tnorm2_gainConj_eq, ct_tnorm2_gainConj_eq]
    dsimp only
    unfold qWt
    ring
  simp only [hEu, hNu, hJu]
  exact real_core γ ν μ.re s1 s2 hν hγ hs1 hs12 ψ hψ hsub hψnn (energyE c b) (energyN c G)
    (energyR c F G) (fun s => ∫ x in UnforcedLeray.B0579.cell c, tnorm2 (F (s, x)) * tnorm2 (G (s, x)))
    hEI hNI hRI hJI hE0 hRJ hcore
