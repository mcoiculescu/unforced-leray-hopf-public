import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_3
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.AdjointSmoothing.WeightedH1
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.AdjointSmoothing.WeightedH1Cont
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.H1Gronwall

/-!
# `PartIII-a:T21/2/7/2/4`: higher regularity of the weak reverse-time adjoint (vocabulary and assembly)

Source of record: `the November 2 reference manuscript`
(SP), lines 3060-3073 (the weighted energies `E_1`, `E_2` used as classical quantities;
`E_1' + β_min E_2 ≤ C_b(E_1 + E_0)` integrated), lines 3052-3058 (the adjoint localized interaction
`K_c^T(φ∇E)` maps `X_{-m,d}` to `H^1_{-m,d}` uniformly), lines 3044-3049 (periodic weight and
logarithmic derivative bounds).

## Route and decomposition

For `ν ≤ 1`, a train with `LadTrainBdd` on every `[0, S]` and `TrainJetsBdd tr m S` (weighted jets
`D^j v`, `j ≤ 6`), and a weak adjoint solution `φ` jointly `C^∞` on `[t, s) × ℝ²`, the target
`AdjointWeakHigherCont m` asks for `AdjHigherCont`:
* `∂^w φ ∈ C([t, s); X_{-m,c})` for `|w| ≤ 3` (`AdjSpatialCont c m t s 3 φ`);
* `∂^w ∂_r φ ∈ C([t, s); X_{-m,c})` for `|w| ≤ 1`.

The proof proceeds by induction on `|w|`:
* The base cases `|w| = 0` (`HigherContAux.adjSpatialCont_zero`, from `IsAdjointWeak`) and `|w| ≤ 1`
  (`HigherContAux.adjSpatialCont_one`, from `AdjointWeakH1` and `AdjointWeakH1Cont`) are proved here.
* `HigherContAux.adjFieldH1Cont_of_source` (proved here) applies the general leaves `CutE1Deriv`,
  `CutRateBound`, `CutE1TimeCont`, `CutSliceProps`, `CutEnergySqueeze`, `L2StrongOfEnergy`,
  `GradEIntegrable` (`Sub/PartIII-a_T21_2_7_2_3.lean`, proved in `Tasks/AdjSmooth/`) and the
  Gronwall step of `Tasks/AdjSmooth/H1Gronwall.lean` to any jointly smooth `c`-periodic field `ψ`
  on `[t, b)` whose effective source `ladChi tr ψ` is bounded in `X_{-m,c}` and whose gradient is
  square-integrable in time on `(t, b]`, yielding `∂_k ψ ∈ C([t, b); X_{-m,c})`.
* The four decomposed leaf propositions:
  1. **`AdjHigherChiBound m`** (`PartIII-a:T21/2/7/2/4/1`): weighted `X_{-m,c}` bound on `∂^w χ`
     (`|w| ≤ k + 1 ≤ 3`, `χ = ladChi tr φ = ∂_r φ + νΔφ + v·∇φ = K_c^T(φ∇E)`) on `(t, b) ⊂ [t, s)`
     from `TrainJetsBdd` (jets `D^j v`, `j ≤ 4`, since `∇E = ∇ curl v`), `adjWChiIdentify`, and
     `ktOrderMinusOneUnif`;
  2. **`AdjHigherSourceBound m`** (`PartIII-a:T21/2/7/2/4/2`): weighted `X_{-m,c}` bound on
     `ladChi tr (fun r => adjSpatial w (φ r))` for `|w| ≤ k ≤ 2` from `∂^w χ` and the transport
     commutator `[∂^w, v·∇]φ` using `TrainJetsBdd` and `AdjSpatialCont`;
  3. **`AdjFieldIntegratedH1 m`** (`PartIII-a:T21/2/7/2/4/3`): integrated `H¹` bound on `(t, b]`
     for any smooth periodic field `ψ` with bounded `X_{-m,c}` norm and bounded `ladChi tr ψ` on
     `(t, b)`, from the `E_0` cutoff energy identity;
  4. **`AdjHigherTimeCont m`** (`PartIII-a:T21/2/7/2/4/4`): `∂^w ∂_r φ ∈ C([t, s); X_{-m,c})` for
     `|w| ≤ 1` from the equation `∂_r φ = χ - νΔφ - v·∇φ` (`ladChi`) and the `|w| ≤ 3` spatial cases
     plus continuity in `r` of `v` and `∇E` in the weighted norm.
* `adjointWeakHigherCont_of_parts` (proved here) assembles `AdjointWeakHigherCont m` from the four
  leaves together with `adjointWeakH1` and `adjointWeakH1Cont`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

/-! ## Spatial regularity predicate -/

/-- **`∂^w φ ∈ C([t, s); X_{-m,c})` for all words `|w| ≤ k`**
(source `the November 2 reference manuscript`
lines 3060-3073). -/
def AdjSpatialCont (c m t s : ℝ) (k : ℕ) (φ : ℝ → ℝ × ℝ → ℂ) : Prop :=
  ∀ r ∈ Ico t s, ∀ w : List (Fin 2), w.length ≤ k →
    MemLp (adjSpatial w (φ r)) 2 (B0579.cellMeasure c (-m)) ∧
    Tendsto (fun r' => xNorm c (-m) (adjSpatial w (φ r') - adjSpatial w (φ r)))
      (𝓝[Ico t s] r) (𝓝 0)

namespace HigherContAux

/-- The transport commutator `[∂^w, v(ρ)·∇] Φ = ∂^w(v(ρ)·∇Φ) - v(ρ)·∇(∂^w Φ)
= Σ_{w₁+w₂=w, w₁≠0} (∂^{w₁}v(ρ))·∇∂^{w₂}Φ` (SP 3067-3071). -/
def adjTransComm {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (ρ : ℝ)
    (w : List (Fin 2)) (Φ : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ :=
  adjSpatial w (ladTransport tr ρ Φ) x - ladTransport tr ρ (adjSpatial w Φ) x

/-- Every spatial derivative word `adjSpatial w φ` of a jointly smooth field on `[t, s) × ℝ²` is
jointly smooth on `[t, s) × ℝ²`. -/
theorem jointSmooth_adjSpatial {t s : ℝ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ)) :
    ∀ w : List (Fin 2),
      ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => adjSpatial w (φ p.1) p.2) (Ico t s ×ˢ univ)
  | [] => hj
  | k :: w => jointSmooth_pdCx (ψ := fun r => adjSpatial w (φ r)) (jointSmooth_adjSpatial hj w) k

/-- Every spatial derivative word `adjSpatial w g` of a `c`-periodic field `g` is `c`-periodic. -/
theorem periodic_adjSpatial {c : ℝ} {g : ℝ × ℝ → ℂ}
    (hper : ∀ x : ℝ × ℝ, g (x.1 + c, x.2) = g x) :
    ∀ (w : List (Fin 2)) (x : ℝ × ℝ), adjSpatial w g (x.1 + c, x.2) = adjSpatial w g x
  | [], x => hper x
  | k :: w, x => by
    have ih := periodic_adjSpatial hper w
    have hfun : (fun y : ℝ × ℝ => adjSpatial w g (y + ((c, 0) : ℝ × ℝ))) = adjSpatial w g := by
      funext y
      have hy : y + ((c, 0) : ℝ × ℝ) = (y.1 + c, y.2) := by ext <;> simp
      rw [hy]
      exact ih y
    have h := fderiv_comp_add_right (𝕜 := ℝ) (f := adjSpatial w g) (x := x) ((c, 0) : ℝ × ℝ)
    rw [hfun] at h
    have hx : x + ((c, 0) : ℝ × ℝ) = (x.1 + c, x.2) := by ext <;> simp
    change pdCx k (adjSpatial w g) (x.1 + c, x.2) = pdCx k (adjSpatial w g) x
    unfold pdCx
    rw [← hx, ← h]

/-- Base case `k = 0`: a weak adjoint lies in `C([t, s); X_{-m,c})`. -/
theorem adjSpatialCont_zero {ν c m : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c} {t s : ℝ}
    {g : ℝ × ℝ → ℂ} {φ : ℝ → ℝ × ℝ → ℂ} (hφ : IsAdjointWeak ν c m tr t s g φ) :
    AdjSpatialCont c m t s 0 φ := by
  intro r hr w hw
  have hw0 : w = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hw)
  subst hw0
  refine ⟨hφ.memX r ⟨hr.1, hr.2.le⟩, ?_⟩
  exact (hφ.strongCont r ⟨hr.1, hr.2.le⟩).mono_left (nhdsWithin_mono _ Ico_subset_Icc_self)

/-- Step `k = 1`: `AdjointWeakH1` and `AdjointWeakH1Cont` give `AdjSpatialCont c m t s 1 φ`. -/
theorem adjSpatialCont_one {m ν : ℝ} (h1 : AdjointWeakH1 m) (hC : AdjointWeakH1Cont m)
    (hν : 0 < ν) (hν1 : ν ≤ 1) {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    (hb : ∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) {t s : ℝ} (ht : 0 ≤ t) (hts : t < s)
    {G : ℝ × ℝ → ℂ}
    (hG : MemLp G 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-m)))
    {φ : ℝ → ℝ × ℝ → ℂ}
    (hφ : IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s (physAdj (clockA ν s) G) φ)
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ)) :
    AdjSpatialCont (ν ^ (-2 : ℝ)) m t s 1 φ := by
  have hm1 := h1 ν hν hν1 tr hb t s ht hts G hG φ hφ hj
  have hc1 := hC ν hν hν1 tr hb t s ht hts G hG φ hφ hj hm1
  intro r hr w hw
  cases w with
  | nil => exact adjSpatialCont_zero hφ r hr [] (Nat.zero_le _)
  | cons k w' =>
    have hw' : w' = [] := List.eq_nil_of_length_eq_zero (by simpa using hw)
    subst hw'
    exact ⟨hm1 r hr k, hc1 r hr k⟩

/-! ### General `H¹` continuity machine for a smooth periodic field `ψ` (`SP` 3060-3073) -/

open H1GronAux in
/-- **Gronwall step for a general smooth periodic field `ψ` on `[t, b)`** (SP 3068-3073): if
`ladChi tr ψ = ∂_ρ ψ + νΔψ + v·∇ψ` is bounded in `X_{-m,c}` on `(t, b)` and
`∫_t^b ‖∂_k ψ(ρ)‖²_{X_{-m,c}} dρ < ∞`, then `∂_k ψ(r) ∈ X_{-m,c}` for every `r ∈ [t, b)`. -/
theorem adjFieldH1Gronwall {m ν t b : ℝ} (hν : 0 < ν)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    (hb : ∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) (ht : 0 ≤ t) (htb : t < b)
    {ψ : ℝ → ℝ × ℝ → ℂ}
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t b ×ˢ univ))
    (hper : ∀ r ∈ Ico t b, ∀ x : ℝ × ℝ, ψ r (x.1 + ν ^ (-2 : ℝ), x.2) = ψ r x)
    {M : ℝ}
    (hM : ∀ ρ ∈ Ioo t b, MemLp (ladChi tr ψ ρ) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ∧
      eLpNorm (ladChi tr ψ ρ) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ≤ ENNReal.ofReal M)
    (hI : ∀ k : Fin 2, ∫⁻ ρ in Ioc t b, (∫⁻ x, ‖pdCx k (ψ ρ) x‖ₑ ^ (2 : ℝ)
      ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) < ⊤) :
    ∀ r ∈ Ico t b, ∀ k : Fin 2,
      MemLp (pdCx k (ψ r)) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := by
  intro r hr k
  have hc0 : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  obtain ⟨CV, hCV⟩ := hb b (ht.trans htb.le)
  obtain ⟨K, hK0, hK⟩ := cutRateBound m ν CV M hν
  have hslice : ∀ ρ ∈ Ico t b, ContDiff ℝ ∞ (ψ ρ) := fun ρ hρ => adjContDiff_slice hj hρ
  have hrate : ∀ R : ℝ, 1 ≤ R → ∀ ρ ∈ Ioo t b,
      -(K * (1 + cutE1 (ν ^ (-2 : ℝ)) m (2 * R) (ψ ρ))) ≤
        cutRate (ν ^ (-2 : ℝ)) m R (ψ ρ) (ladDt ψ ρ) := by
    intro R hR ρ hρ
    have hρ' : ρ ∈ Ico t b := Ioo_subset_Ico_self hρ
    have hρS : ρ ∈ Icc (0 : ℝ) b := ⟨ht.trans hρ.1.le, hρ.2.le⟩
    obtain ⟨h1, _⟩ := hK _ R (ψ ρ) (ladChi tr ψ ρ) (ladDt ψ ρ)
      (fun x j => tr.v ρ x j) hc0 hR (hslice ρ hρ') (continuous_ladChi tr ht hj hρ)
      (continuous_ladDt hj hρ) (fun x hx j => (hCV ρ hρS x hx).1 j)
      (fun x => by
        have e : ladChi tr ψ ρ x = ladDt ψ ρ x + (ν : ℂ) * ladLapCx (ψ ρ) x +
            ladTransport tr ρ (ψ ρ) x := rfl
        rw [e]
        unfold ladTransport
        ring)
      (hM ρ hρ).1 (hM ρ hρ).2
    have hl := CutSliceAux.cutLap_nonneg (ν ^ (-2 : ℝ)) m R (ψ ρ)
    nlinarith [mul_nonneg hν.le hl]
  have hmeas : ∀ k : Fin 2, AEMeasurable (fun ρ => gk (ν ^ (-2 : ℝ)) m (ψ ρ) k)
      (volume.restrict (Ioo r b)) := fun k => aemeasurable_gk hj hr.1 k
  have hIoo : ∀ k : Fin 2, ∫⁻ ρ in Ioo r b, gk (ν ^ (-2 : ℝ)) m (ψ ρ) k < ⊤ := fun k =>
    lt_of_le_of_lt (lintegral_mono_set (Ioo_subset_Ioc_self.trans (Ioc_subset_Ioc_left hr.1)))
      (hI k)
  have hfin : ∀ k : Fin 2, ∀ᵐ ρ ∂(volume.restrict (Ioo r b)), gk (ν ^ (-2 : ℝ)) m (ψ ρ) k < ⊤ :=
    fun k => ae_lt_top' (hmeas k) (hIoo k).ne
  have hB' : ∫⁻ ρ in Ioo r b, (gk (ν ^ (-2 : ℝ)) m (ψ ρ) 0 + gk (ν ^ (-2 : ℝ)) m (ψ ρ) 1) < ⊤ := by
    rw [lintegral_add_left' (hmeas 0)]
    exact ENNReal.add_lt_top.2 ⟨hIoo 0, hIoo 1⟩
  have hex : ∃ r' ∈ Ioo r b, ∀ k : Fin 2, gk (ν ^ (-2 : ℝ)) m (ψ r') k < ⊤ := by
    have h1 : ∀ᵐ ρ ∂(volume.restrict (Ioo r b)),
        ρ ∈ Ioo r b ∧ ∀ k : Fin 2, gk (ν ^ (-2 : ℝ)) m (ψ ρ) k < ⊤ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo, hfin 0, hfin 1] with ρ h0 h1 h2
      exact ⟨h0, fun k => by fin_cases k <;> assumption⟩
    have : (ae (volume.restrict (Ioo r b))).NeBot := by
      rw [ae_neBot]
      intro h
      have := Measure.restrict_eq_zero.1 h
      rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at this
      linarith [hr.2]
    obtain ⟨ρ, h⟩ := h1.exists
    exact ⟨ρ, h⟩
  obtain ⟨r', hr'I, hr'g⟩ := hex
  have hr'Ico : ∀ ρ ∈ Icc r r', ρ ∈ Ico t b := fun ρ hρ =>
    ⟨hr.1.trans hρ.1, lt_of_le_of_lt hρ.2 hr'I.2⟩
  have hint : ∀ R : ℝ, 0 < R →
      ∫ y in r..r', cutE1 (ν ^ (-2 : ℝ)) m R (ψ y) ≤
        (∫⁻ ρ in Ioo r b, (gk (ν ^ (-2 : ℝ)) m (ψ ρ) 0 + gk (ν ^ (-2 : ℝ)) m (ψ ρ) 1)).toReal := by
    intro R hR
    have hcont : ContinuousOn (fun y => cutE1 (ν ^ (-2 : ℝ)) m R (ψ y)) (Ioo r r') :=
      (cutE1TimeCont _ m R t b ψ hc0 hR hj).1.mono
        (fun ρ hρ => hr'Ico ρ ⟨hρ.1.le, hρ.2.le⟩)
    rw [intervalIntegral.integral_of_le hr'I.1.le, integral_Ioc_eq_integral_Ioo,
      integral_eq_lintegral_of_nonneg_ae
        (ae_of_all _ fun y => CutSliceAux.cutE1_nonneg _ m R (ψ y))
        (hcont.aestronglyMeasurable measurableSet_Ioo)]
    refine ENNReal.toReal_mono hB'.ne ?_
    calc ∫⁻ y in Ioo r r', ENNReal.ofReal (cutE1 (ν ^ (-2 : ℝ)) m R (ψ y))
        ≤ ∫⁻ y in Ioo r r', (gk (ν ^ (-2 : ℝ)) m (ψ y) 0 + gk (ν ^ (-2 : ℝ)) m (ψ y) 1) := by
          refine lintegral_mono_ae ?_
          have h' := ae_restrict_of_ae_restrict_of_subset
            (Ioo_subset_Ioo_right hr'I.2.le) ((hfin 0).and (hfin 1))
          filter_upwards [h', ae_restrict_mem measurableSet_Ioo] with y hy hyI
          have hle := cutE1_le_gk (hslice y (hr'Ico y ⟨hyI.1.le, hyI.2.le⟩)) hR
            (fun k => by fin_cases k; exacts [hy.1, hy.2])
          rw [Fin.sum_univ_two] at hle
          calc ENNReal.ofReal (cutE1 (ν ^ (-2 : ℝ)) m R (ψ y))
              ≤ ENNReal.ofReal ((gk (ν ^ (-2 : ℝ)) m (ψ y) 0).toReal +
                (gk (ν ^ (-2 : ℝ)) m (ψ y) 1).toReal) := ENNReal.ofReal_le_ofReal hle
            _ = gk (ν ^ (-2 : ℝ)) m (ψ y) 0 + gk (ν ^ (-2 : ℝ)) m (ψ y) 1 := by
              rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
                ENNReal.ofReal_toReal hy.1.ne, ENNReal.ofReal_toReal hy.2.ne]
      _ ≤ ∫⁻ y in Ioo r b, (gk (ν ^ (-2 : ℝ)) m (ψ y) 0 + gk (ν ^ (-2 : ℝ)) m (ψ y) 1) :=
          lintegral_mono_set (Ioo_subset_Ioo_right hr'I.2.le)
  have hbound : ∀ n : ℕ, cutE1 (ν ^ (-2 : ℝ)) m ((n : ℝ) + 1) (ψ r) ≤
      ((gk (ν ^ (-2 : ℝ)) m (ψ r') 0).toReal + (gk (ν ^ (-2 : ℝ)) m (ψ r') 1).toReal) +
        K * ((r' - r) + (∫⁻ ρ in Ioo r b, (gk (ν ^ (-2 : ℝ)) m (ψ ρ) 0 +
          gk (ν ^ (-2 : ℝ)) m (ψ ρ) 1)).toReal) := by
    intro n
    have hR0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hR1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hcont1 : ContinuousOn (fun y => cutE1 (ν ^ (-2 : ℝ)) m ((n : ℝ) + 1) (ψ y)) (Icc r r') :=
      (cutE1TimeCont _ m _ t b ψ hc0 hR0 hj).1.mono hr'Ico
    have hcont2 : ContinuousOn (fun y => cutE1 (ν ^ (-2 : ℝ)) m (2 * ((n : ℝ) + 1)) (ψ y))
        (Icc r r') :=
      (cutE1TimeCont _ m _ t b ψ hc0 (by positivity) hj).1.mono hr'Ico
    have hineq := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le
      (a := r) (b := r') (g := fun ρ => cutE1 (ν ^ (-2 : ℝ)) m ((n : ℝ) + 1) (ψ ρ))
      (g' := fun ρ => cutRate (ν ^ (-2 : ℝ)) m ((n : ℝ) + 1) (ψ ρ) (ladDt ψ ρ))
      (φ := fun ρ => -(K * (1 + cutE1 (ν ^ (-2 : ℝ)) m (2 * ((n : ℝ) + 1)) (ψ ρ))))
      hr'I.1.le hcont1
      (fun x hx => (cutE1Deriv _ m _ t b ψ hc0 hR0 hj hper x
        ⟨lt_of_le_of_lt hr.1 hx.1, hx.2.trans hr'I.2⟩).hasDerivWithinAt)
      ((continuousOn_const.add hcont2).const_mul K |>.neg |>.integrableOn_Icc)
      (fun x hx => hrate _ hR1 x ⟨lt_of_le_of_lt hr.1 hx.1, hx.2.trans hr'I.2⟩)
    have hEint : IntervalIntegrable
        (fun y => cutE1 (ν ^ (-2 : ℝ)) m (2 * ((n : ℝ) + 1)) (ψ y)) volume r r' :=
      (hcont2.mono (by rw [uIcc_of_le hr'I.1.le])).intervalIntegrable
    have hval : ∫ y in r..r', -(K * (1 + cutE1 (ν ^ (-2 : ℝ)) m (2 * ((n : ℝ) + 1)) (ψ y))) =
        -(K * ((r' - r) + ∫ y in r..r',
          cutE1 (ν ^ (-2 : ℝ)) m (2 * ((n : ℝ) + 1)) (ψ y))) := by
      rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add intervalIntegrable_const hEint]
      simp
    rw [hval] at hineq
    have hI2 := hint (2 * ((n : ℝ) + 1)) (by positivity)
    have hr'E := cutE1_le_gk (hslice r' ⟨hr'I.1.le.trans' hr.1, hr'I.2⟩) hR0 hr'g
    rw [Fin.sum_univ_two] at hr'E
    nlinarith [mul_le_mul_of_nonneg_left hI2 hK0]
  exact memLp_of_lt_top (CutSliceAux.contDiff_pdCx (hslice r hr) k).continuous
    (gk_lt_top_of_bdd (hslice r hr) hbound k)

/-- **Strong `H¹` continuity for a general smooth periodic field `ψ` on `[t, b)`** (SP 3060-3073):
combines `adjFieldH1Gronwall` with `CutE1Deriv`, `CutRateBound`, `CutE1TimeCont`, `CutSliceProps`,
`CutEnergySqueeze`, `L2StrongOfEnergy`, `GradEIntegrable`. -/
theorem adjFieldH1Cont_of_source {m ν t b : ℝ} (hν : 0 < ν)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    (hb : ∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) (ht : 0 ≤ t) (htb : t < b)
    {ψ : ℝ → ℝ × ℝ → ℂ}
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t b ×ˢ univ))
    (hper : ∀ r ∈ Ico t b, ∀ x : ℝ × ℝ, ψ r (x.1 + ν ^ (-2 : ℝ), x.2) = ψ r x)
    {M : ℝ}
    (hM : ∀ ρ ∈ Ioo t b, MemLp (ladChi tr ψ ρ) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ∧
      eLpNorm (ladChi tr ψ ρ) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ≤ ENNReal.ofReal M)
    (hI : ∀ k : Fin 2, ∫⁻ ρ in Ioc t b, (∫⁻ x, ‖pdCx k (ψ ρ) x‖ₑ ^ (2 : ℝ)
      ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) < ⊤) :
    ∀ r ∈ Ico t b, ∀ k : Fin 2,
      MemLp (pdCx k (ψ r)) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ∧
      Tendsto (fun r' => xNorm (ν ^ (-2 : ℝ)) (-m) (pdCx k (ψ r') - pdCx k (ψ r)))
        (𝓝[Ico t b] r) (𝓝 0) := by
  have hm := adjFieldH1Gronwall hν hb ht htb hj hper hM hI
  intro r hr k
  refine ⟨hm r hr k, ?_⟩
  have hc0 : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  obtain ⟨CV, hCV⟩ := hb b (ht.trans htb.le)
  obtain ⟨K, hK0, hK⟩ := cutRateBound m ν CV M hν
  have hslice : ∀ ρ ∈ Ico t b, ContDiff ℝ ∞ (ψ ρ) := fun ρ hρ => adjContDiff_slice hj hρ
  have hn1 : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hEc : ContinuousOn (fun ρ => gradE (ν ^ (-2 : ℝ)) m (ψ ρ)) (Ico t b) := by
    refine cutEnergySqueeze t b ν K (fun n ρ => cutE1 (ν ^ (-2 : ℝ)) m ((n : ℝ) + 1) (ψ ρ))
      (fun n ρ => cutLap (ν ^ (-2 : ℝ)) m ((n : ℝ) + 1) (ψ ρ)) _ htb hν hK0
      (fun n => (cutE1TimeCont _ m _ t b ψ hc0 (hn1 n) hj).1)
      (fun n => (cutE1TimeCont _ m _ t b ψ hc0 (hn1 n) hj).2)
      (fun n ρ hρ => ((cutSliceProps _ m _ hc0 (hslice ρ hρ)).1 _ (hn1 n)).1)
      (fun n ρ hρ => ((cutSliceProps _ m _ hc0 (hslice ρ hρ)).1 _ (hn1 n)).2)
      (fun ρ hρ n n' hnn => (cutSliceProps _ m _ hc0 (hslice ρ hρ)).2.1 _ _ (hn1 n) (by
        have : (n : ℝ) ≤ n' := by exact_mod_cast hnn
        linarith))
      (fun ρ hρ => ((cutSliceProps _ m _ hc0 (hslice ρ hρ)).2.2 (hm ρ hρ)).2)
      (gradEIntegrable _ m t b ψ hc0 htb hj hm hI)
      ?_
    intro n ρ hρ
    have hρ' : ρ ∈ Ico t b := Ioo_subset_Ico_self hρ
    have hρS : ρ ∈ Icc (0 : ℝ) b := ⟨ht.trans hρ.1.le, hρ.2.le⟩
    have hR : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    obtain ⟨h1, h2⟩ := hK _ ((n : ℝ) + 1) (ψ ρ) (ladChi tr ψ ρ) (ladDt ψ ρ)
      (fun x j => tr.v ρ x j) hc0 hR (hslice ρ hρ') (continuous_ladChi tr ht hj hρ)
      (continuous_ladDt hj hρ) (fun x hx j => (hCV ρ hρS x hx).1 j)
      (fun x => by
        have e : ladChi tr ψ ρ x = ladDt ψ ρ x + (ν : ℂ) * ladLapCx (ψ ρ) x +
            ladTransport tr ρ (ψ ρ) x := rfl
        rw [e]
        unfold ladTransport
        ring)
      (hM ρ hρ).1 (hM ρ hρ).2
    have hle : cutE1 (ν ^ (-2 : ℝ)) m (2 * ((n : ℝ) + 1)) (ψ ρ) ≤
        gradE (ν ^ (-2 : ℝ)) m (ψ ρ) :=
      ((cutSliceProps _ m _ hc0 (hslice ρ hρ')).2.2 (hm ρ hρ')).1 _ (by positivity)
    have hle2 : K * (1 + cutE1 (ν ^ (-2 : ℝ)) m (2 * ((n : ℝ) + 1)) (ψ ρ)) ≤
        K * (1 + gradE (ν ^ (-2 : ℝ)) m (ψ ρ)) :=
      mul_le_mul_of_nonneg_left (by linarith) hK0
    exact ⟨_, cutE1Deriv _ m _ t b ψ hc0 (hn1 n) hj hper ρ hρ, by linarith, by linarith⟩
  have hcw : Tendsto (fun ρ => gradE (ν ^ (-2 : ℝ)) m (ψ ρ)) (𝓝[Ico t b] r)
      (𝓝 (gradE (ν ^ (-2 : ℝ)) m (ψ r))) := hEc r hr
  exact l2StrongOfEnergy (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) (𝓝[Ico t b] r)
    (fun r' k => pdCx k (ψ r')) (fun k => pdCx k (ψ r))
    (by filter_upwards [self_mem_nhdsWithin] with r' hr' k using hm r' hr' k)
    (fun k => hm r hr k) (fun k x => tendsto_pdCx_slice hj hr k x) hcw k

/-- Continuous `X_{-m,c}`-norm on a compact sub-interval `[t, b] ⊆ [t, s)` is bounded. -/
theorem exists_xNorm_bdd_on_Ioo {c m t s b : ℝ} {f : ℝ → ℝ × ℝ → ℂ} (hb : b ∈ Ioo t s)
    (hm : ∀ r ∈ Ico t s, MemLp (f r) 2 (B0579.cellMeasure c (-m)))
    (hc : ∀ r ∈ Ico t s, Tendsto (fun r' => xNorm c (-m) (f r' - f r)) (𝓝[Ico t s] r) (𝓝 0)) :
    ∃ M₀ : ℝ, ∀ ρ ∈ Ioo t b,
      eLpNorm (f ρ) 2 (B0579.cellMeasure c (-m)) ≤ ENNReal.ofReal M₀ := by
  have hsub : Icc t b ⊆ Ico t s := fun r hr => ⟨hr.1, lt_of_le_of_lt hr.2 hb.2⟩
  have hcont : ContinuousOn (fun r => (xNorm c (-m) (f r)).toReal) (Icc t b) := by
    intro r hr
    have hr' : r ∈ Ico t s := hsub hr
    rw [ContinuousWithinAt, Metric.tendsto_nhds]
    intro ε hε
    have h1 : ∀ᶠ r' in 𝓝[Icc t b] r, xNorm c (-m) (f r' - f r) < ENNReal.ofReal ε :=
      ((hc r hr').mono_left (nhdsWithin_mono _ hsub)).eventually
        (Iio_mem_nhds (ENNReal.ofReal_pos.2 hε))
    have h2 : ∀ᶠ r' in 𝓝[Icc t b] r, r' ∈ Icc t b := self_mem_nhdsWithin
    filter_upwards [h1, h2] with r' hr'1 hr'2
    have hmr' := hm r' (hsub hr'2)
    have hmr := hm r hr'
    have hfr : f r' = f r' - f r + f r := by ext x; simp
    have hle1 : xNorm c (-m) (f r') ≤ xNorm c (-m) (f r' - f r) + xNorm c (-m) (f r) := by
      have := eLpNorm_add_le (hmr'.sub hmr).1 hmr.1 (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      rwa [← hfr] at this
    have hfr2 : f r = f r - f r' + f r' := by ext x; simp
    have hle2 : xNorm c (-m) (f r) ≤ xNorm c (-m) (f r' - f r) + xNorm c (-m) (f r') := by
      have hsymm : xNorm c (-m) (f r - f r') = xNorm c (-m) (f r' - f r) := by
        have e : f r - f r' = -(f r' - f r) := by ext x; simp
        rw [e, xNorm, eLpNorm_neg]
        rfl
      have := eLpNorm_add_le (hmr.sub hmr').1 hmr'.1 (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      rw [← hfr2] at this
      change xNorm c (-m) (f r) ≤ xNorm c (-m) (f r - f r') + xNorm c (-m) (f r') at this
      rwa [hsymm] at this
    have hfin_diff : xNorm c (-m) (f r' - f r) ≠ ⊤ := (hmr'.sub hmr).2.ne
    have hfin_r' : xNorm c (-m) (f r') ≠ ⊤ := hmr'.2.ne
    have hfin_r : xNorm c (-m) (f r) ≠ ⊤ := hmr.2.ne
    have ht1 : (xNorm c (-m) (f r')).toReal ≤
        (xNorm c (-m) (f r' - f r)).toReal + (xNorm c (-m) (f r)).toReal := by
      rw [← ENNReal.toReal_add hfin_diff hfin_r]
      exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin_diff, hfin_r⟩) hle1
    have ht2 : (xNorm c (-m) (f r)).toReal ≤
        (xNorm c (-m) (f r' - f r)).toReal + (xNorm c (-m) (f r')).toReal := by
      rw [← ENNReal.toReal_add hfin_diff hfin_r']
      exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin_diff, hfin_r'⟩) hle2
    have hlt : (xNorm c (-m) (f r' - f r)).toReal < ε := by
      rw [← ENNReal.toReal_ofReal hε.le]
      exact (ENNReal.toReal_lt_toReal hfin_diff ENNReal.ofReal_ne_top).2 hr'1
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith, by linarith⟩
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨M₀, fun ρ hρ => ?_⟩
  have hρc : ρ ∈ Icc t b := ⟨hρ.1.le, hρ.2.le⟩
  have hfin : xNorm c (-m) (f ρ) ≠ ⊤ := (hm ρ (hsub hρc)).2.ne
  change xNorm c (-m) (f ρ) ≤ ENNReal.ofReal M₀
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hM₀ ρ hρc))

end HigherContAux

/-! ## The four decomposed leaf propositions -/

/-- **(ii) Weighted `X_{-m,c}` bound on `∂^w χ` from the train jets**
(source `the November 2 reference manuscript`
lines 3052-3058: the adjoint localized interaction `χ = ladChi tr φ = K_c^T(φ∇E)` is of order `-1`;
`∇E = ∇ curl v`, so `∂^{w'}∇E` for `|w'| ≤ 2` uses only `D^j v` for `j ≤ 4 ≤ 6` from
`TrainJetsBdd`). If `∂^u φ ∈ C([t, s); X_{-m,c})` for `|u| ≤ k` (`k ≤ 2`), then on every
`[t, b] ⊂ [t, s)` the spatial partials `∂^w χ(ρ)`, `|w| ≤ k + 1`, are bounded in `X_{-m,c}`
uniformly for `ρ ∈ (t, b)`. -/
def AdjHigherChiBound (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    (∀ S : ℝ, 0 ≤ S → TrainJetsBdd tr m S) →
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ G : ℝ × ℝ → ℂ,
      MemLp G 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-m)) →
      ∀ φ : ℝ → ℝ × ℝ → ℂ,
        IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s (physAdj (clockA ν s) G) φ →
        ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ) →
        ∀ k : ℕ, k ≤ 2 → AdjSpatialCont (ν ^ (-2 : ℝ)) m t s k φ →
        ∀ b ∈ Ioo t s, ∃ M : ℝ, ∀ ρ ∈ Ioo t b, ∀ w : List (Fin 2), w.length ≤ k + 1 →
          MemLp (adjSpatial w (ladChi tr φ ρ)) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ∧
          eLpNorm (adjSpatial w (ladChi tr φ ρ)) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ≤
            ENNReal.ofReal M

/-- **(i-a) Effective source bound for `ψ = ∂^w φ`**
(source `the November 2 reference manuscript`
lines 3067-3071): for `|w| ≤ k ≤ 2`,
`ladChi tr (∂^w φ) = ∂_ρ(∂^w φ) + νΔ(∂^w φ) + v·∇(∂^w φ) = ∂^w χ - [∂^w, v·∇]φ`
(`∂^w χ - Σ_{w₁+w₂=w, w₁≠0} (∂^{w₁}v)·∇∂^{w₂}φ`), which is bounded in `X_{-m,c}` on `(t, b)` by
the bound on `∂^w χ` (`AdjHigherChiBound`) and the commutator bound from `TrainJetsBdd` (`|w₁| ≤ 2`)
and `AdjSpatialCont` (`|w₂| + 1 ≤ |w| ≤ k`). -/
def AdjHigherSourceBound (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    (∀ S : ℝ, 0 ≤ S → TrainJetsBdd tr m S) →
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ φ : ℝ → ℝ × ℝ → ℂ,
      ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ) →
      (∀ r ∈ Ico t s, ∀ x : ℝ × ℝ, φ r (x.1 + ν ^ (-2 : ℝ), x.2) = φ r x) →
      ∀ k : ℕ, k ≤ 2 → AdjSpatialCont (ν ^ (-2 : ℝ)) m t s k φ →
      ∀ b ∈ Ioo t s, ∀ Mχ : ℝ,
        (∀ ρ ∈ Ioo t b, ∀ w : List (Fin 2), w.length ≤ k →
          MemLp (adjSpatial w (ladChi tr φ ρ)) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ∧
          eLpNorm (adjSpatial w (ladChi tr φ ρ)) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ≤
            ENNReal.ofReal Mχ) →
        ∀ w : List (Fin 2), w.length ≤ k → ∃ M : ℝ, ∀ ρ ∈ Ioo t b,
          MemLp (ladChi tr (fun r => adjSpatial w (φ r)) ρ) 2
            (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ∧
          eLpNorm (ladChi tr (fun r => adjSpatial w (φ r)) ρ) 2
            (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ≤ ENNReal.ofReal M

/-- **(i-b) Integrated `H¹` bound on `[t, b]` for a smooth periodic field `ψ ∈ C([t, s); X_{-m,c})`
with bounded source**
(source `the November 2 reference manuscript`
lines 3060-3067: the `E_0` cutoff energy identity `d/dρ (cutE0 R ψ) ≥ ν cutE1 R ψ - K(1 + cutE0 (2R) ψ)`
integrated on `[t, b]`, `b < s`, where `‖ψ(ρ)‖_{X_{-m,c}}` is bounded by continuity on the compact
`[t, b]`). -/
def AdjFieldIntegratedH1 (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    ∀ t b : ℝ, 0 ≤ t → t < b → ∀ ψ : ℝ → ℝ × ℝ → ℂ,
      ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t b ×ˢ univ) →
      (∀ r ∈ Ico t b, ∀ x : ℝ × ℝ, ψ r (x.1 + ν ^ (-2 : ℝ), x.2) = ψ r x) →
      (∀ r ∈ Ico t b, MemLp (ψ r) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) →
      (∃ M₀ : ℝ, ∀ ρ ∈ Ioo t b,
        eLpNorm (ψ ρ) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ≤ ENNReal.ofReal M₀) →
      (∃ M : ℝ, ∀ ρ ∈ Ioo t b,
        MemLp (ladChi tr ψ ρ) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ∧
        eLpNorm (ladChi tr ψ ρ) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ≤ ENNReal.ofReal M) →
      ∀ j : Fin 2, ∫⁻ ρ in Ioc t b, (∫⁻ x, ‖pdCx j (ψ ρ) x‖ₑ ^ (2 : ℝ)
        ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) < ⊤

/-- **(i) Induction step for general multi-index `w`, `|w| ≤ 3`**
(source `the November 2 reference manuscript`
lines 3060-3073): if `∂^{w'} φ ∈ C([t, s); X_{-m,c})` for `|w'| ≤ k` (`k ≤ 2`), then
`∂^w φ ∈ C([t, s); X_{-m,c})` for `|w| ≤ k + 1`. -/
def AdjHigherStep (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    (∀ S : ℝ, 0 ≤ S → TrainJetsBdd tr m S) →
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ G : ℝ × ℝ → ℂ,
      MemLp G 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-m)) →
      ∀ φ : ℝ → ℝ × ℝ → ℂ,
        IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s (physAdj (clockA ν s) G) φ →
        ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ) →
        ∀ k : ℕ, k ≤ 2 → AdjSpatialCont (ν ^ (-2 : ℝ)) m t s k φ →
          AdjSpatialCont (ν ^ (-2 : ℝ)) m t s (k + 1) φ

/-- **(iii) Time derivative continuity `∂^w ∂_r φ ∈ C([t, s); X_{-m,c})` for `|w| ≤ 1`**
(source `the November 2 reference manuscript`
lines 3060-3073): from the equation `∂_r φ = χ - νΔφ - v·∇φ` (`ladChi`), the spatial continuity
`∂^w φ ∈ C([t, s); X_{-m,c})` for `|w| ≤ 3`, and the continuity in `r` of `v` and `∇E` in the
weighted norm (`TrainJetsBdd`). -/
def AdjHigherTimeCont (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    (∀ S : ℝ, 0 ≤ S → TrainJetsBdd tr m S) →
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ G : ℝ × ℝ → ℂ,
      MemLp G 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-m)) →
      ∀ φ : ℝ → ℝ × ℝ → ℂ,
        IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s (physAdj (clockA ν s) G) φ →
        ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ) →
        AdjSpatialCont (ν ^ (-2 : ℝ)) m t s 3 φ →
        ∀ r ∈ Ico t s, ∀ w : List (Fin 2), w.length ≤ 1 →
          MemLp (adjSpatial w (adjDt t s φ r)) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ∧
          Tendsto (fun r' => xNorm (ν ^ (-2 : ℝ)) (-m)
              (adjSpatial w (adjDt t s φ r') - adjSpatial w (adjDt t s φ r)))
            (𝓝[Ico t s] r) (𝓝 0)

/-! ## Conditional assemblies -/

open HigherContAux in
/-- **`AdjHigherStep` from `AdjHigherChiBound`, `AdjHigherSourceBound`, and `AdjFieldIntegratedH1`**
(SP 3060-3073): applies `adjFieldH1Cont_of_source` to `ψ = adjSpatial w φ` on `[t, b)` with
`b = (r + s) / 2`. -/
theorem adjHigherStep_of (m : ℝ) (hChi : AdjHigherChiBound m) (hSrc : AdjHigherSourceBound m)
    (hInt : AdjFieldIntegratedH1 m) : AdjHigherStep m := by
  intro ν hν hν1 tr hb hJ t s ht hts G hG φ hφ hj k hk hSp r hr w hw
  rcases Nat.lt_or_ge w.length (k + 1) with hlt | hge
  · exact hSp r hr w (Nat.lt_succ_iff.1 hlt)
  · cases w with
    | nil => simp at hge
    | cons j w₀ =>
      have hw₀ : w₀.length ≤ k := by simp at hw; omega
      set b := (r + s) / 2 with hb_def
      have hbIoo : b ∈ Ioo t s := ⟨by linarith [hr.1, hr.2], by linarith [hr.2]⟩
      have htb : t < b := hbIoo.1
      have hrb : r ∈ Ico t b := ⟨hr.1, by linarith [hr.2]⟩
      have hsub : Ico t b ×ˢ (univ : Set (ℝ × ℝ)) ⊆ Ico t s ×ˢ univ :=
        fun p hp => ⟨⟨hp.1.1, hp.1.2.trans hbIoo.2⟩, hp.2⟩
      set ψ : ℝ → ℝ × ℝ → ℂ := fun r' => adjSpatial w₀ (φ r')
      have hjψ : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t b ×ˢ univ) :=
        (jointSmooth_adjSpatial hj w₀).mono hsub
      have hperψ : ∀ r' ∈ Ico t b, ∀ x : ℝ × ℝ, ψ r' (x.1 + ν ^ (-2 : ℝ), x.2) = ψ r' x :=
        fun r' hr' x => periodic_adjSpatial (hφ.periodic r' ⟨hr'.1, hr'.2.trans hbIoo.2⟩) w₀ x
      obtain ⟨Mχ, hMχ⟩ := hChi ν hν hν1 tr hb hJ t s ht hts G hG φ hφ hj k hk hSp b hbIoo
      obtain ⟨M, hM⟩ := hSrc ν hν hν1 tr hb hJ t s ht hts φ hj hφ.periodic k hk hSp b hbIoo Mχ
        (fun ρ hρ u hu => hMχ ρ hρ u (hu.trans (Nat.le_succ k))) w₀ hw₀
      obtain ⟨M₀, hM₀⟩ := exists_xNorm_bdd_on_Ioo (f := ψ) hbIoo
        (fun r' hr' => (hSp r' hr' w₀ hw₀).1) (fun r' hr' => (hSp r' hr' w₀ hw₀).2)
      have hI : ∀ j' : Fin 2, ∫⁻ ρ in Ioc t b, (∫⁻ x, ‖pdCx j' (ψ ρ) x‖ₑ ^ (2 : ℝ)
          ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) < ⊤ :=
        hInt ν hν hν1 tr hb t b ht htb ψ hjψ hperψ
          (fun r' hr' => (hSp r' ⟨hr'.1, hr'.2.trans hbIoo.2⟩ w₀ hw₀).1)
          ⟨M₀, hM₀⟩ ⟨M, hM⟩
      obtain ⟨hm_j, hc_j⟩ := adjFieldH1Cont_of_source hν hb ht htb hjψ hperψ hM hI r hrb j
      refine ⟨hm_j, ?_⟩
      have hnhds : 𝓝[Ico t b] r = 𝓝[Ico t s] r := by
        apply nhdsWithin_eq_nhdsWithin' (Iio_mem_nhds hrb.2)
        ext x
        simp only [mem_inter_iff, mem_Ico, mem_Iio]
        exact ⟨fun h => ⟨⟨h.1.1, h.2.trans hbIoo.2⟩, h.2⟩, fun h => ⟨⟨h.1.1, h.2⟩, h.2⟩⟩
      rwa [hnhds] at hc_j

open HigherContAux in
/-- **`AdjointWeakHigherCont` from the induction step `AdjHigherStep` and the time-derivative step
`AdjHigherTimeCont`** (with the base cases from `AdjointWeakH1` and `AdjointWeakH1Cont`,
SP 3060-3073). -/
theorem adjointWeakHigherCont_of (m : ℝ) (h1 : AdjointWeakH1 m) (hC : AdjointWeakH1Cont m)
    (hStep : AdjHigherStep m) (hTime : AdjHigherTimeCont m) :
    AdjointWeakHigherCont m := by
  intro ν hν hν1 tr hb hJ t s ht hts G hG φ hφ hj
  have hSp1 : AdjSpatialCont (ν ^ (-2 : ℝ)) m t s 1 φ :=
    adjSpatialCont_one h1 hC hν hν1 hb ht hts hG hφ hj
  have hSp2 : AdjSpatialCont (ν ^ (-2 : ℝ)) m t s 2 φ :=
    hStep ν hν hν1 tr hb hJ t s ht hts G hG φ hφ hj 1 (by decide) hSp1
  have hSp3 : AdjSpatialCont (ν ^ (-2 : ℝ)) m t s 3 φ :=
    hStep ν hν hν1 tr hb hJ t s ht hts G hG φ hφ hj 2 (by decide) hSp2
  intro r hr w
  exact ⟨fun hw => hSp3 r hr w hw, fun hw => hTime ν hν hν1 tr hb hJ t s ht hts G hG φ hφ hj hSp3 r hr w hw⟩

/-- Conditional assembly of `AdjointWeakHigherCont m` from the base cases (`adjointWeakH1`,
`adjointWeakH1Cont`), the induction step `AdjHigherStep m`, and the time-derivative step
`AdjHigherTimeCont m`. -/
theorem adjointWeakHigherCont_of_step_and_time (m : ℝ) (hm : 8 < m)
    (hStep : AdjHigherStep m) (hTime : AdjHigherTimeCont m) :
    UnforcedLeray.Short.IIIa.AdjointWeakHigherCont m :=
  adjointWeakHigherCont_of m (adjointWeakH1 m hm) (adjointWeakH1Cont m hm) hStep hTime

/-- Conditional assembly of `AdjointWeakHigherCont m` from the four leaf propositions
`AdjHigherChiBound m`, `AdjHigherSourceBound m`, `AdjFieldIntegratedH1 m`, and
`AdjHigherTimeCont m`. -/
theorem adjointWeakHigherCont_of_parts (m : ℝ) (hm : 8 < m)
    (hChi : AdjHigherChiBound m) (hSrc : AdjHigherSourceBound m)
    (hInt : AdjFieldIntegratedH1 m) (hTime : AdjHigherTimeCont m) :
    UnforcedLeray.Short.IIIa.AdjointWeakHigherCont m :=
  adjointWeakHigherCont_of m (adjointWeakH1 m hm) (adjointWeakH1Cont m hm)
    (adjHigherStep_of m hChi hSrc hInt) hTime

end UnforcedLeray.Short.IIIa
