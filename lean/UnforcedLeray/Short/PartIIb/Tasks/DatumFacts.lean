import UnforcedLeray.Short.PartIIb.StatementsNonlinear
import UnforcedLeray.Short.PartIIb.Sub.B3
import UnforcedLeray.Short.PartIIb.Tasks.DatumFacts.RawDatumSmooth
import UnforcedLeray.Cons.C03Background.Scheme

/-!
# `PartII-b:B2`: regularity, solenoidality, scaling, nonvanishing, and `L^{3,∞} ∩ L²_loc` of the datum

Source of record: `the November 2 reference manuscript`, lines 2563–2600.

For every state `z : p.Z` in the contraction ball (`‖z‖ ≤ C₁ ν^{-k₁} e^{m/ν} ε^{3/11}` with
`2 m < 3 d₋ / 11`), the common DSS datum `a := p.datum (p.coord z)` satisfies:
* `Cons.C03.IsB3Datum p.period a` and `Cons.C03.IsB3DatumOffZero p.period a`:
  smooth off `0`, divergence-free off `0` and distributionally solenoidal on all of `ℝ³`,
  nonzero off `0`, discretely self-similar with ratio `e^{P/2}`, satisfying the inverse-distance
  derivative bounds `‖D^k a(x)‖ · ‖x‖^{k+1} ≤ C_k` (`k ≤ 4`), and axisymmetric without swirl;
* weak-`L³` (`L^{3,∞}(ℝ³)`) and local `L²` (`L²_loc(ℝ³)`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint UnforcedLeray.Axi
open UnforcedLeray.Short.IIb.DatumFactsAux

namespace DatumFactsAux

/-- Evaluating `partialEta` on a differentiable stream `Ψ` via the one-variable derivative in `η`. -/
theorem partialEta_eq_of_hasDerivAt {Ψ : ℝ × ℝ → ℝ} {w : ℝ × ℝ} {d : ℝ}
    (hΨ : DifferentiableAt ℝ Ψ w) (hd : HasDerivAt (fun t : ℝ => Ψ (w.1, t)) d w.2) :
    partialEta Ψ w = d := by
  have h1 : HasDerivAt (fun t : ℝ => (w.1, t)) (0, 1) w.2 :=
    (hasDerivAt_const w.2 w.1).prodMk (hasDerivAt_id w.2)
  have h2 : HasDerivAt (fun t : ℝ => Ψ (w.1, t)) (fderiv ℝ Ψ w (0, 1)) w.2 :=
    hΨ.hasFDerivAt.comp_hasDerivAt w.2 h1
  exact h2.unique hd

/-- At `(0, 1)`, `partialEta (B0140.trainStream c) (0, 1) ≥ e^{-1/4}` for every `c > 0`. -/
theorem partialEta_trainStream_zero_one_ge {c : ℝ} (hc : 0 < c) :
    Real.exp (-1 / 4) ≤ partialEta (UnforcedLeray.B0140.trainStream c) (0, 1) := by
  have hc0 : c ≠ 0 := hc.ne'
  have hψ_cd : ContDiff ℝ ∞ (UnforcedLeray.B0140.trainStream c) := by
    have heq : UnforcedLeray.B0140.trainStream c =
        fun z : ℝ × ℝ => UnforcedLeray.Short.PartIIa.trainDatum c z.1 z.2 :=
      funext fun z => (UnforcedLeray.Short.PartIIa.trainDatum_eq_trainStream c z.1 z.2).symm
    rw [heq]
    exact UnforcedLeray.Short.PartIIa.InletDivZeroAux.contDiff_trainDatum hc0
  have hd : DifferentiableAt ℝ (UnforcedLeray.B0140.trainStream c) (0, 1) :=
    hψ_cd.differentiable (by simp) (0, 1)
  have hη : partialEta (UnforcedLeray.B0140.trainStream c) (0, 1) =
      -(UnforcedLeray.B0140.trainVelocity c (0, 1)).1 :=
    partialEta_eq_of_hasDerivAt hd (UnforcedLeray.B0140.hasDerivAt_trainStream_η hc0 (0, 1))
  rw [hη, UnforcedLeray.B0140.trainVelocity_eq_latticeSum hc0 (0, 1)]
  dsimp only
  have hsum : HasSum
      (fun n : ℤ => -(UnforcedLeray.GaussianVortex.velocity ((0 : ℝ) - n * c, (1 : ℝ))).1)
      (-UnforcedLeray.B0146.latticeSum c (fun w => (UnforcedLeray.GaussianVortex.velocity w).1) (0, 1)) :=
    (UnforcedLeray.B0140.xdecay_velocity_fst.hasSum hc0 (0, 1)).neg
  have hterm_nonneg : ∀ n : ℤ,
      0 ≤ -(UnforcedLeray.GaussianVortex.velocity ((0 : ℝ) - n * c, (1 : ℝ))).1 := by
    intro n
    rw [UnforcedLeray.B0140.velocity_apply]
    simp only [Prod.smul_mk, smul_eq_mul, mul_neg, mul_one, neg_neg]
    positivity
  have h0 := le_hasSum hsum (0 : ℤ) (fun n _ => hterm_nonneg n)
  have h0_eq : -(UnforcedLeray.GaussianVortex.velocity ((0 : ℝ) - (0 : ℤ) * c, (1 : ℝ))).1 =
      Real.exp (-1 / 4) := by
    rw [UnforcedLeray.B0140.velocity_apply]
    simp only [Int.cast_zero, zero_mul, sub_zero, Prod.smul_mk, smul_eq_mul]
    ring_nf
  rwa [h0_eq] at h0

/-- The `0`-th coordinate of `p.datum α` at `x = !₂[p.R, 0, 1]` is `-partialEta (p.datumStream α) (0, 1)`. -/
theorem datum_eval_core_zero (p : Params) (α : Fin 2 → ℝ) :
    p.datum α (!₂[p.R, 0, 1]) 0 = -partialEta (p.datumStream α) (0, 1) := by
  set x : Space := !₂[p.R, 0, 1] with hx
  have hx0 : x 0 = p.R := by simp [hx]
  have hx1 : x 1 = 0 := by simp [hx]
  have hx2 : x 2 = 1 := by simp [hx]
  have hR0 : p.R ≠ 0 := p.R_pos.ne'
  have hϱ : Axi.ϱ x = p.R := by
    unfold Axi.ϱ
    rw [hx0, hx1]
    simp [Real.sqrt_sq p.R_pos.le]
  have hage : Axi.age p.R x = 1 := by
    unfold Axi.age
    rw [hϱ, div_self (pow_ne_zero 2 hR0)]
  have hchart : (Axi.chart p.R 0 x).2 = (0, 1) := by
    unfold Axi.chart Axi.phase Axi.trans
    rw [hage, hϱ, hx2]
    simp [div_self hR0]
  have heR0 : Axi.eR x 0 = 1 := by
    simp [Axi.eR, Axi.hor, hϱ, hx0, inv_mul_cancel₀ hR0]
  have he30 : Axi.e3 0 = 0 := by
    simp [Axi.e3]
  unfold Params.datum Axi.Nv Axi.frameL
  dsimp only
  rw [hage, hchart, Real.sqrt_one, one_smul]
  simp [datumProfile, Axi.m0, Axi.m1, heR0, he30]

/-- Bound on `|p.coord z i|` from `‖z‖ ≤ C₁ ν^{-k₁} e^{m/ν} ε^{3/11}`. -/
theorem abs_coord_le {dm dp m C₁ : ℝ} {k₁ : ℕ} {p : Params} {d : ℝ}
    (hreg : BgRegime p d dm dp) {z : p.Z}
    (hz : ‖z‖ ≤ C₁ * (p.ν ^ k₁)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ)) (i : Fin 2) :
    |p.coord z i| ≤ C₁ * (p.ν ^ k₁)⁻¹ * Real.exp (-((dm - m) / p.ν)) := by
  have hνpos : 0 < p.ν := p.ν_pos
  have hεpos : 0 < p.ε := p.ε_pos
  have hε8_nonneg : 0 ≤ p.ε ^ (8 / 11 : ℝ) := Real.rpow_nonneg hεpos.le _
  have hcA : |cA p.period (z : Amb p.period) i| ≤ ‖z‖ := by
    have hA : ‖cA p.period (z : Amb p.period)‖ ≤ ‖(z : Amb p.period)‖ := by
      rw [norm_amb]
      linarith [norm_nonneg (cw p.period (z : Amb p.period)),
        norm_nonneg (cΔ p.period (z : Amb p.period)),
        norm_nonneg (cT p.period (z : Amb p.period))]
    have hz_eq : ‖(z : Amb p.period)‖ = ‖z‖ := rfl
    have hi := PiLp.norm_apply_le (cA p.period (z : Amb p.period)) i
    rw [Real.norm_eq_abs] at hi
    linarith
  have h1 : |p.coord z i| ≤ p.ε ^ (8 / 11 : ℝ) * ‖z‖ := by
    unfold Params.coord
    rw [abs_mul, abs_of_nonneg hε8_nonneg]
    exact mul_le_mul_of_nonneg_left hcA hε8_nonneg
  have h2 : p.ε ^ (8 / 11 : ℝ) * ‖z‖ ≤
      C₁ * (p.ν ^ k₁)⁻¹ * (Real.exp (m / p.ν) * p.ε) := by
    calc p.ε ^ (8 / 11 : ℝ) * ‖z‖
        ≤ p.ε ^ (8 / 11 : ℝ) * (C₁ * (p.ν ^ k₁)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ)) :=
          mul_le_mul_of_nonneg_left hz hε8_nonneg
      _ = C₁ * (p.ν ^ k₁)⁻¹ * Real.exp (m / p.ν) * (p.ε ^ (8 / 11 : ℝ) * p.ε ^ (3 / 11 : ℝ)) := by ring
      _ = C₁ * (p.ν ^ k₁)⁻¹ * (Real.exp (m / p.ν) * p.ε) := by
          rw [← Real.rpow_add hεpos, show (8 / 11 : ℝ) + 3 / 11 = 1 by norm_num, Real.rpow_one]
          ring
  have h3 : Real.exp (m / p.ν) * p.ε ≤ Real.exp (-((dm - m) / p.ν)) := by
    rw [hreg.eps_eq, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have hdm : dm ≤ d := hreg.dm_le
    have : m / p.ν + -d / p.ν = -((d - m) / p.ν) := by ring
    rw [this, neg_le_neg_iff]
    exact div_le_div_of_nonneg_right (by linarith) hνpos.le
  have hC_nonneg : 0 ≤ C₁ * (p.ν ^ k₁)⁻¹ := by
    have h0 : 0 ≤ ‖z‖ := norm_nonneg z
    have hpos : 0 < Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) := by positivity
    have hle : 0 ≤ (C₁ * (p.ν ^ k₁)⁻¹) * (Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ)) := by
      linarith [h0, hz]
    exact nonneg_of_mul_nonneg_left hle hpos
  exact h1.trans (h2.trans (mul_le_mul_of_nonneg_left h3 hC_nonneg))

/-- Elementary polynomial-vs-exponential absorption: for `δ > 0`, `ν > 0` and `K : ℕ`,
`(ν ^ K)⁻¹ * exp (-δ / ν) ≤ (K + 1)! / δ ^ (K + 1) * ν`. -/
theorem inv_pow_mul_exp_neg_le {δ ν : ℝ} (hδ : 0 < δ) (hν : 0 < ν) (K : ℕ) :
    (ν ^ K)⁻¹ * Real.exp (-(δ / ν)) ≤ ((K + 1).factorial : ℝ) / δ ^ (K + 1) * ν := by
  have hx : 0 ≤ δ / ν := by positivity
  have hexp := Real.pow_div_factorial_le_exp (δ / ν) hx (K + 1)
  have hfac : (0 : ℝ) < (K + 1).factorial := Nat.cast_pos.2 (Nat.factorial_pos _)
  have hpow : (δ / ν) ^ (K + 1) / ((K + 1).factorial : ℝ) =
      (δ ^ (K + 1) / ((K + 1).factorial : ℝ)) * (ν ^ K * ν)⁻¹ := by
    rw [div_pow, pow_succ, div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [hpow] at hexp
  have hpos2 : 0 < ν ^ K * Real.exp (δ / ν) := by positivity
  have hinv_eq : (ν ^ K)⁻¹ * Real.exp (-(δ / ν)) = (ν ^ K * Real.exp (δ / ν))⁻¹ := by
    rw [Real.exp_neg, mul_inv]
  rw [hinv_eq, inv_le_iff_one_le_mul₀' hpos2]
  have hmul := mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ ((K + 1).factorial : ℝ) / δ ^ (K + 1) * (ν ^ K * ν))
  have hcancel1 : ((K + 1).factorial : ℝ) / δ ^ (K + 1) * (ν ^ K * ν) *
      (δ ^ (K + 1) / ((K + 1).factorial : ℝ) * (ν ^ K * ν)⁻¹) = 1 := by
    have hδ0 : δ ^ (K + 1) ≠ 0 := pow_ne_zero _ hδ.ne'
    have hν0 : ν ^ K * ν ≠ 0 := mul_ne_zero (pow_ne_zero _ hν.ne') hν.ne'
    field_simp [hfac.ne']
  rw [hcancel1] at hmul
  calc (1 : ℝ) ≤ ((K + 1).factorial : ℝ) / δ ^ (K + 1) * (ν ^ K * ν) * Real.exp (δ / ν) := hmul
    _ = (ν ^ K * Real.exp (δ / ν)) * (((K + 1).factorial : ℝ) / δ ^ (K + 1) * ν) := by ring

end DatumFactsAux

/-- Full datum regularity package for `a := p.datum (p.coord z)` (`PartII-b:B2`, SP 2563–2600):
`IsB3Datum`, `IsB3DatumOffZero`, weak-`L³`, and `L²_loc`. -/
def IsRegularDatum (p : Params) (a : SpatialField) : Prop :=
  Cons.C03.IsB3Datum p.period a ∧
  Cons.C03.IsB3DatumOffZero p.period a ∧
  (∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 < t →
    volume {x : Space | t ≤ ‖a x‖} ≤ ENNReal.ofReal (K * t⁻¹ ^ 3)) ∧
  (∀ r : ℝ, MemLp a 2 (volume.restrict (Metric.ball 0 r)))

/-- **`PartII-b:B2` (`DatumFacts`)**: at fixed slow data `Σ > 0` and growing eigenpair `(λ, q)`,
for every `0 < m` with `2 m < 3 d₋ / 11` and ball constants `C₁ > 0, k₁`, there is `ν₀ > 0`
such that for `p.ν ≤ ν₀`, `p.ageCut = Σ`, `p.mode = q`, every state `z : p.Z` with
`‖z‖ ≤ C₁ ν^{-k₁} e^{m/ν} ε^{3/11}` has `IsRegularDatum p (p.datum (p.coord z))`. -/
def DatumFacts : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ m : ℝ, 0 < m → ∀ dm dp : ℝ, 0 < dm → 2 * m < 3 * dm / 11 → ∀ (C₁ : ℝ) (k₁ : ℕ), 0 < C₁ →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ z : p.Z,
      ‖z‖ ≤ C₁ * (p.ν ^ k₁)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) →
      IsRegularDatum p (p.datum (p.coord z))

/-- Proof of `DatumFacts` (`PartII-b:B2`). -/
theorem datum_facts : DatumFacts := by
  intro Sig lam q _hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨Cf, γf, Nf, hCf, hγf, hfro_jet⟩ := frozenStreamJets lam q hq 1
  obtain ⟨_, _, _, -, -, hper0⟩ := frozenStreamBounds lam q hq 0
  have hδ : 0 < dm - m := by linarith
  set K : ℕ := k₁ + 2 * Nf
  set B : ℝ := C₁ * Cf * (((K + 1).factorial : ℝ) / (dm - m) ^ (K + 1))
  have hB : 0 < B := by positivity
  set ν₀ : ℝ := min 1 (min dm (Real.exp (-1 / 4) / 8 * B⁻¹))
  have hν₀ : 0 < ν₀ := by positivity
  refine ⟨ν₀, hν₀, fun p d hreg hν _hag hmode z hz => ?_⟩
  have hν1 : p.ν ≤ 1 := hν.trans (min_le_left _ _)
  have hνdm : p.ν ≤ dm := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hνB : p.ν ≤ Real.exp (-1 / 4) / 8 * B⁻¹ :=
    hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hR2 : 2 ≤ p.R := by
    unfold Params.R
    rw [hreg.eps_eq, ← Real.exp_neg, neg_div, neg_neg]
    have h1 : 1 ≤ dm / p.ν := (one_le_div p.ν_pos).2 hνdm
    have h2 : dm / p.ν ≤ d / p.ν := div_le_div_of_nonneg_right hreg.dm_le p.ν_pos.le
    have h3 := Real.add_one_le_exp (d / p.ν)
    linarith
  have hc1 : 1 ≤ p.c := by
    rw [hreg.c_eq, one_le_inv₀ (pow_pos p.ν_pos 2)]
    nlinarith [p.ν_pos, hν1]
  have hc0 : 0 < p.c := lt_of_lt_of_le one_pos hc1
  set α := p.coord z
  have hsm : ContDiffOn ℝ ∞ (p.datum α) {0}ᶜ :=
    contDiffOn_datum hq hreg hν1 hR2 hmode α
  have hdiv : ∀ x : Space, x ≠ 0 → Axi.divergence (p.datum α) x = 0 :=
    fun x hx => divergence_datum_eq_zero hq hreg hν1 hR2 hmode α hx
  have hbds : ∀ k : ℕ, k ≤ 4 → ∃ C : ℝ, ∀ x : Space, x ≠ 0 →
      ‖iteratedFDeriv ℝ k (p.datum α) x‖ * ‖x‖ ^ (k + 1) ≤ C :=
    fun k _ => bounds_datum hq hreg hν1 hR2 hmode α k
  have hnz : ∃ x : Space, x ≠ 0 ∧ p.datum α x ≠ 0 := by
    refine ⟨!₂[p.R, 0, 1], ?_, ?_⟩
    · intro h0
      have h2 : (!₂[p.R, 0, 1] : Space) 2 = (0 : Space) 2 := congrArg (fun v : Space => v 2) h0
      simp at h2
    · intro h0
      have hval0 : p.datum α (!₂[p.R, 0, 1]) 0 = 0 := by rw [h0]; simp
      rw [datum_eval_core_zero p α] at hval0
      have hψ0_eq : p.train.ψ 0 = UnforcedLeray.B0140.trainStream p.c :=
        p.train.isTrain.stream_zero hc1
      have hψ0_cd : ContDiff ℝ ∞ (UnforcedLeray.B0140.trainStream p.c) := by
        have heq : UnforcedLeray.B0140.trainStream p.c =
            fun w : ℝ × ℝ => UnforcedLeray.Short.PartIIa.trainDatum p.c w.1 w.2 :=
          funext fun w => (UnforcedLeray.Short.PartIIa.trainDatum_eq_trainStream p.c w.1 w.2).symm
        rw [heq]
        exact UnforcedLeray.Short.PartIIa.InletDivZeroAux.contDiff_trainDatum hc0.ne'
      have hfro_cd : ∀ i : Fin 2, ContDiff ℝ ∞ (p.frozenStream i) :=
        fun i => inletCD_frozenStream (hper0 p.c hc1).1 hmode i
      have hd0 : DifferentiableAt ℝ (UnforcedLeray.B0140.trainStream p.c) (0, 1) :=
        hψ0_cd.differentiable (by simp) (0, 1)
      have hdf0 : DifferentiableAt ℝ (p.frozenStream 0) (0, 1) :=
        (hfro_cd 0).differentiable (by simp) (0, 1)
      have hdf1 : DifferentiableAt ℝ (p.frozenStream 1) (0, 1) :=
        (hfro_cd 1).differentiable (by simp) (0, 1)
      have hstream_eq : p.datumStream α = fun w =>
          UnforcedLeray.B0140.trainStream p.c w +
            (α 0 * p.frozenStream 0 w + α 1 * p.frozenStream 1 w) := by
        funext w
        unfold Params.datumStream
        rw [hψ0_eq, Fin.sum_univ_two]
      have hfd : fderiv ℝ (p.datumStream α) (0, 1) =
          fderiv ℝ (UnforcedLeray.B0140.trainStream p.c) (0, 1) +
            (α 0 • fderiv ℝ (p.frozenStream 0) (0, 1) +
              α 1 • fderiv ℝ (p.frozenStream 1) (0, 1)) := by
        rw [hstream_eq]
        exact (hd0.hasFDerivAt.add
          ((hdf0.hasFDerivAt.const_mul (α 0)).add (hdf1.hasFDerivAt.const_mul (α 1)))).fderiv
      have hη_split : partialEta (p.datumStream α) (0, 1) =
          partialEta (UnforcedLeray.B0140.trainStream p.c) (0, 1) +
            (α 0 * partialEta (p.frozenStream 0) (0, 1) +
              α 1 * partialEta (p.frozenStream 1) (0, 1)) := by
        unfold partialEta
        rw [hfd]
        simp [add_apply, smul_apply, smul_eq_mul]
      have hfro_eta : ∀ i : Fin 2, |α i * partialEta (p.frozenStream i) (0, 1)| ≤
          Real.exp (-1 / 4) / 8 := by
        intro i
        have h1 : |partialEta (p.frozenStream i) (0, 1)| ≤ Cf * p.c ^ Nf := by
          unfold partialEta
          have hnorm01 : ‖((0 : ℝ), (1 : ℝ))‖ = 1 := by
            simp [Prod.norm_def]
          have hle1 : ‖fderiv ℝ (p.frozenStream i) (0, 1) (0, 1)‖ ≤
              ‖fderiv ℝ (p.frozenStream i) (0, 1)‖ * ‖((0 : ℝ), (1 : ℝ))‖ :=
            ContinuousLinearMap.le_opNorm _ _
          rw [hnorm01, mul_one, ← norm_iteratedFDeriv_one] at hle1
          have hle2 := hfro_jet p hmode hc1 i 1 le_rfl (0, 1)
          have hexp_le : Real.exp (-(γf * |(0, 1).2| / p.c)) ≤ 1 := by
            apply Real.exp_le_one_iff.2
            have : 0 ≤ γf * |(0, 1).2| / p.c := by positivity
            linarith
          have hle3 : Cf * p.c ^ Nf * Real.exp (-(γf * |(0, 1).2| / p.c)) ≤
              Cf * p.c ^ Nf * 1 :=
            mul_le_mul_of_nonneg_left hexp_le (by positivity)
          rw [Real.norm_eq_abs] at hle1
          linarith
        have hcoord_le := abs_coord_le hreg hz i
        have hνpos : 0 < p.ν := p.ν_pos
        have hprod : |α i * partialEta (p.frozenStream i) (0, 1)| ≤
            C₁ * Cf * ((p.ν ^ K)⁻¹ * Real.exp (-((dm - m) / p.ν))) := by
          rw [abs_mul]
          have hmul := mul_le_mul hcoord_le h1 (abs_nonneg _) (by positivity)
          have hc_pow : p.c ^ Nf = (p.ν ^ (2 * Nf))⁻¹ := by
            rw [hreg.c_eq, inv_pow, ← pow_mul]
          have hν_pow : (p.ν ^ k₁)⁻¹ * (p.ν ^ (2 * Nf))⁻¹ = (p.ν ^ K)⁻¹ := by
            rw [← mul_inv, ← pow_add]
          calc |α i| * |partialEta (p.frozenStream i) (0, 1)|
              ≤ C₁ * (p.ν ^ k₁)⁻¹ * Real.exp (-((dm - m) / p.ν)) * (Cf * p.c ^ Nf) := hmul
            _ = C₁ * Cf * ((p.ν ^ k₁)⁻¹ * (p.ν ^ (2 * Nf))⁻¹ * Real.exp (-((dm - m) / p.ν))) := by
                rw [hc_pow]; ring
            _ = C₁ * Cf * ((p.ν ^ K)⁻¹ * Real.exp (-((dm - m) / p.ν))) := by rw [hν_pow]
        have habsorb := inv_pow_mul_exp_neg_le hδ p.ν_pos K
        have hprod2 : C₁ * Cf * ((p.ν ^ K)⁻¹ * Real.exp (-((dm - m) / p.ν))) ≤ B * p.ν := by
          have := mul_le_mul_of_nonneg_left habsorb (by positivity : 0 ≤ C₁ * Cf)
          linarith
        have hBν : B * p.ν ≤ Real.exp (-1 / 4) / 8 := by
          calc B * p.ν ≤ B * (Real.exp (-1 / 4) / 8 * B⁻¹) :=
                mul_le_mul_of_nonneg_left hνB hB.le
            _ = Real.exp (-1 / 4) / 8 * (B * B⁻¹) := by ring
            _ = Real.exp (-1 / 4) / 8 := by rw [mul_inv_cancel₀ hB.ne', mul_one]
        exact hprod.trans (hprod2.trans hBν)
      have htr := partialEta_trainStream_zero_one_ge hc0
      have hf0 := (abs_le.1 (hfro_eta 0)).1
      have hf1 := (abs_le.1 (hfro_eta 1)).1
      have hpos_exp : 0 < Real.exp (-1 / 4) := Real.exp_pos _
      linarith
  have hoff : Cons.C03.IsB3DatumOffZero p.period (p.datum α) :=
    { smooth := hsm
      div_free := hdiv
      nonzero := hnz
      dss := fun x _ => p.datum_dss α x
      bounds := hbds
      symmetric := p.datum_symmetric α }
  obtain ⟨C0, hC0⟩ := hbds 0 (Nat.zero_le _)
  have hC0' : ∀ x : Space, x ≠ 0 → ‖p.datum α x‖ * ‖x‖ ≤ C0 := by
    intro x hx
    have h := hC0 x hx
    rwa [norm_iteratedFDeriv_zero, zero_add, pow_one] at h
  exact ⟨hoff.toIsB3Datum, hoff, weakL3_of_inv_norm_bound hC0',
    memLp_two_loc_of_inv_norm_bound hsm.continuousOn hC0'⟩

/-- `datum_facts` wrapped in `B3Stmt.AtBallStates` for direct use in `PartII-b:B3`. -/
theorem datum_facts_atBallStates :
    B3Stmt.AtBallStates (fun p z => IsRegularDatum p (p.datum (p.coord z))) := by
  intro Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₀, hν₀, H⟩ := datum_facts Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  exact ⟨ν₀, hν₀, fun p d hreg hν hS hq' z _hPE hzn => H p d hreg hν hS hq' z hzn⟩

#print axioms datum_facts

end UnforcedLeray.Short.IIb
