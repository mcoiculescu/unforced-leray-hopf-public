import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Estimates
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.Scale
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Young
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.N0
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymMu

/-!
# Decomposition of `actualJet` (`PartIII-b:C/rep/6`, source 5389-5413, `repair:actual-jet`)

Source: `the November 2 reference manuscript` lines 5389-5413 (with the kernel
bounds 4917-4937).

The audited jet bound `jetEps1` (`Concrete/SourceL/Ambient/JetEps1.lean`) is stated with the
*uncut* moment `N₀(M) = ∫_{u>1.2/ν} u^{-3/2}⨍|M|`, which is **not** controlled by
`N = N₁(χ_o T₁)` (the cutoff `χ_o` is small on `1.2/ν < u < 1.5/ν`).  The source bound (4917-4927:
`|Σ_M| ≤ χ_o |E|`, 5400) needs the cut moment

`oldN0w c ν χ_o M = ∫_{u>1.2/ν} u^{-3/2} χ_o(νu) ⨍|M|`.

`actualJet_of` reduces the target to
* `JetEps1W`: the `ε = 1` jet bound with `oldN0w` in place of `N₀` (same proof as `jetEps1`,
  with `phaseB` kept instead of dropping `χ_o ≤ 1` in `phaseB_lintegral_bint`);
* `N0wLeN1`: `oldN0w ≤ N₁(χ_oM)` (Cauchy-Schwarz in `q`, weight `1 + |η|/√s ≥ 1`);
and the audited `lptScale`, `sourceLYoung`, `sourceLN0`, `mu_eventually_mem`, `retNu_tendsto`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The cut old moment `N₀^χ(M) = ∫_{u>1.2/ν} u^{-3/2} χ_o(νu) ∫ |M(u,x)| d(dq dη/c)`
(source 4924-4927 with the cutoff `χ_o` of the phase mean `E`, 4766-4770). -/
def oldN0w (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) : ℝ :=
  ∫ u in Ioi (6 / 5 / ν), u ^ (-(3 / 2 : ℝ)) *
    (χo (ν * u) * ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c))

/-- The `ε = 1` jet bound with the cut moment (source 4917-4937, 5400-5413). -/
def JetEps1W (K : Set ℝ) (χo χy : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ (c ν μ : ℝ), LHyp c ν 1 μ χo χy → μ ∈ K →
    ∀ M : Chart → Mat3, OldThinFinite c ν M → ∀ s : ℝ, 0 < s → ∀ j : ℕ, j ≤ 6 →
      frob (sDerivIter j (Lpt c ν 1 μ χo χy M) s) ≤ C * s ^ (5 / 2 : ℝ) * oldN0w c ν χo M

/-- `N₀^χ(M) ≤ N₁(χ_oM)` (source 5400; `IIIa.firstMoment`): Cauchy-Schwarz in `q`
(`⨍|M| dq ≤ (⨍|M|² dq)^{1/2}`) and `1 + |η|/√s ≥ 1`; `χ_o(νs) = 0` for `s ≤ 1.2/ν`. -/
def N0wLeN1 : Prop :=
  ∀ (c ν : ℝ) (χo : ℝ → ℝ), 0 < c → 0 < ν → IsOutwardCutoff χo →
    ∀ M : Chart → Mat3, OldThinFinite c ν M →
      ENNReal.ofReal (oldN0w c ν χo M) ≤
        UnforcedLeray.Short.IIIa.firstMoment c 0 (fun p => χo (ν * p.1) • M p)

theorem rj6_frob_smul (a : ℝ) (A : Mat3) : frob (a • A) = |a| * frob A := by
  unfold frob
  have : ∀ i j, (a • A) i j ^ 2 = a ^ 2 * A i j ^ 2 := fun i j => by
    simp [Pi.smul_apply, mul_pow]
  simp only [this, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

theorem rj6_sDerivIter_smul (a : ℝ) (f : ℝ → Mat3) (j : ℕ) :
    sDerivIter j (fun s => a • f s) = fun s => a • sDerivIter j f s := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show sDeriv (sDerivIter j (fun s => a • f s)) = fun s => a • sDeriv (sDerivIter j f) s
    rw [ih]
    funext s
    unfold sDeriv
    rw [deriv_fun_const_smul_field]
    exact smul_comm _ _ _

theorem rj6_oldN0w_nonneg (c ν : ℝ) (hν : 0 < ν) {χo : ℝ → ℝ} (hχ : IsOutwardCutoff χo) (M : Chart → Mat3) :
    0 ≤ oldN0w c ν χo M := by
  unfold oldN0w
  refine setIntegral_nonneg measurableSet_Ioi fun u hu => ?_
  have ha : (0 : ℝ) < 6 / 5 / ν := div_pos (by norm_num) hν
  have hu0 : 0 < u := ha.trans hu
  exact mul_nonneg (Real.rpow_nonneg hu0.le _)
    (mul_nonneg (hχ.range _).1 (integral_nonneg fun x => Real.sqrt_nonneg _))

/-- One regime: the jet bound from `JetEps1W` and `N0wLeN1`. -/
theorem rj6_actualJetAt (Pl : UnforcedLeray.Blueprint.Planar.PlanarData) (K : ReturnConsts)
    (L : ReturnLevel) (μ : ℝ) (Kset : Set ℝ) (hμK : μ ∈ Kset) (hν1 : L.ν ≤ 1) (hμ0 : 0 < μ)
    (hμ1 : μ < 1 / 4) (hmZ : 3 / 2 < K.mZ) (hγ : 0 < gRate Pl) (hχy : IsStreamCutoff K.χy)
    {C1 : ℝ}
    (hJ : ∀ (c ν μ : ℝ), LHyp c ν 1 μ K.χo K.χy → μ ∈ Kset →
      ∀ M : Chart → Mat3, OldThinFinite c ν M → ∀ s : ℝ, 0 < s → ∀ j : ℕ, j ≤ 6 →
        frob (sDerivIter j (Lpt c ν 1 μ K.χo K.χy M) s) ≤ C1 * s ^ (5 / 2 : ℝ) * oldN0w c ν K.χo M)
    (hN : N0wLeN1) {C : ℝ} (hC : C1 ≤ C) (hC0 : 0 < C) :
    ActualJetAt Pl K L μ C 0 := by
  intro T
  obtain ⟨CN, kN, hCN⟩ := sourceLN0 K.mZ (gRate Pl) hmZ hγ
  have hfin : OldThinFinite (cOf L.ν) L.ν (thinRep T) :=
    (hCN (cOf L.ν) L.ν (L.ρb Pl K) (cOf_pos L.ν_pos) L.ν_pos hν1 T).1
  have hL1 : LHyp (cOf L.ν) L.ν 1 μ K.χo K.χy :=
    ⟨cOf_pos L.ν_pos, L.ν_pos, hν1, one_pos, hμ0, hμ1, K.hχo, hχy⟩
  have hLε : LHyp (cOf L.ν) L.ν L.ε μ K.χo K.χy :=
    ⟨cOf_pos L.ν_pos, L.ν_pos, hν1, L.ε_pos, hμ0, hμ1, K.hχo, hχy⟩
  refine ⟨?_, ?_⟩
  · intro j hj s hs
    have hfun : LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T =
        fun s => L.ε ^ 3 • Lpt (cOf L.ν) L.ν 1 μ K.χo K.χy (thinRep T) s :=
      funext fun s => Scale.lptScale (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) L.ε_pos s
    rw [hfun, rj6_sDerivIter_smul, rj6_frob_smul, abs_of_pos (pow_pos L.ε_pos 3)]
    have h1 := hJ (cOf L.ν) L.ν μ hL1 hμK (thinRep T) hfin s hs j hj
    have hN0 := hN (cOf L.ν) L.ν K.χo (cOf_pos L.ν_pos) L.ν_pos K.hχo (thinRep T) hfin
    have hpow : 0 ≤ s ^ (5 / 2 : ℝ) := Real.rpow_nonneg hs.le _
    have hεp : 0 ≤ L.ε ^ 3 := (pow_pos L.ε_pos 3).le
    have hw : 0 ≤ oldN0w (cOf L.ν) L.ν K.χo (thinRep T) := rj6_oldN0w_nonneg _ _ L.ν_pos K.hχo _
    have hstep : L.ε ^ 3 * frob (sDerivIter j (Lpt (cOf L.ν) L.ν 1 μ K.χo K.χy (thinRep T)) s) ≤
        C * L.ν⁻¹ ^ 0 * L.ε ^ 3 * s ^ (5 / 2 : ℝ) * oldN0w (cOf L.ν) L.ν K.χo (thinRep T) := by
      have h2 : L.ε ^ 3 * frob (sDerivIter j (Lpt (cOf L.ν) L.ν 1 μ K.χo K.χy (thinRep T)) s) ≤
          L.ε ^ 3 * (C1 * s ^ (5 / 2 : ℝ) * oldN0w (cOf L.ν) L.ν K.χo (thinRep T)) :=
        mul_le_mul_of_nonneg_left h1 hεp
      have h3 : C1 * s ^ (5 / 2 : ℝ) * oldN0w (cOf L.ν) L.ν K.χo (thinRep T) ≤
          C * s ^ (5 / 2 : ℝ) * oldN0w (cOf L.ν) L.ν K.χo (thinRep T) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hpow) hw
      calc _ ≤ _ := h2
        _ ≤ L.ε ^ 3 * (C * s ^ (5 / 2 : ℝ) * oldN0w (cOf L.ν) L.ν K.χo (thinRep T)) :=
            mul_le_mul_of_nonneg_left h3 hεp
        _ = _ := by simp only [pow_zero, mul_one]; ring
    calc ENNReal.ofReal (L.ε ^ 3 * frob (sDerivIter j (Lpt (cOf L.ν) L.ν 1 μ K.χo K.χy
            (thinRep T)) s))
        ≤ ENNReal.ofReal (C * L.ν⁻¹ ^ 0 * L.ε ^ 3 * s ^ (5 / 2 : ℝ) *
            oldN0w (cOf L.ν) L.ν K.χo (thinRep T)) := ENNReal.ofReal_le_ofReal hstep
      _ ≤ ENNReal.ofReal (C * L.ν⁻¹ ^ 0 * L.ε ^ 3 * s ^ (5 / 2 : ℝ)) *
            ENNReal.ofReal (oldN0w (cOf L.ν) L.ν K.χo (thinRep T)) := by
          rw [← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (by simpa using hC0.le) hεp) hpow)]
      _ ≤ _ := by
          gcongr
          exact hN0
  · intro s hs
    exact sourceLYoung (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy hLε hmZ hγ T s hs

/-- **`actualJet` from the two kernel facts.** -/
theorem actualJet_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (hJ : ∀ (K : Set ℝ) (χo χy : ℝ → ℝ), JetEps1W K χo χy) (hN : N0wLeN1) : D.ActualJet := by
  obtain ⟨C1, hC1⟩ := hJ Set.univ D.K.χo D.K.χy
  refine ⟨max C1 1, 0, ?_⟩
  have hν : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ 1 :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (Iic_mem_nhds (by norm_num))
  filter_upwards [hν, mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt] with n hn hm z hz
  have hmz := hm z hz
  have hs := hst.sigma_pos
  have hs1 := hst.sigma_lt
  exact rj6_actualJetAt D.Pl D.K (D.level n) (D.mu n z) Set.univ (Set.mem_univ _) hn
    (by linarith [hmz.1]) (by linarith [hmz.2]) hst.mZ_gt hst.gamma_pos hst.chiY
    (fun c ν μ h _ M hM s hs0 j hj => hC1 c ν μ h (Set.mem_univ _) M hM s hs0 j hj)
    hN (le_max_left _ _) (lt_of_lt_of_le one_pos (le_max_right _ _))

end UnforcedLeray.Short.PartIIIb.Concrete
