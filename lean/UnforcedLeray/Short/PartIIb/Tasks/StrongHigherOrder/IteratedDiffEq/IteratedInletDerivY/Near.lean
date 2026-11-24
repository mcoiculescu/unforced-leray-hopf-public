import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S2_1
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.IteratedDiffEq.RawAllDerivsBdd
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.IteratedDiffEq.RawResidualIteratedEnvelope.Calc
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_2.InletProfileJets3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_2.Shell.Main
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_2_2.DerivBound

/-!
# Near-axis all-order bound for `inletSrc` (`PartII-b:S2/1/3`)

Source of record: `the November 2 reference manuscript`,
lines 2545-2551, 2563-2569, 1206-1222.

Proves:
1. `inletProfileJetsAll` and `inletENearJetsAll`: all-order near-axis axial decay of
   `p.Efun i` and `dτ (p.Efun i)` on `ϱ ≤ R0`, with threshold `ν₀ = 1` independent of order.
2. `norm_iteratedFDeriv_Sfun_le`: all-order spatial derivative bound on `Jets.Sfun`.
3. `inletNearAll`: for any `R0 > 0` and any `m : ℕ`, `β : Fin m → Fin 3`,
   `‖iterDyRev β (inletSrc p i) (τ, y)‖ ≤ C * (1 + |y 2|) ^ (-2 : ℝ)` on `ϱ y ≤ R0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff
open UnforcedLeray.Cons.C03.Concrete (Params)
open UnforcedLeray.Blueprint UnforcedLeray.Axi UnforcedLeray.B0412
open UnforcedLeray.Short.PartIIIb.Concrete

namespace UnforcedLeray.Short.IIb.IterInletSub

/-- All-order `InletProfileJets` with threshold `ν₀ = 1` independent of `K`. -/
theorem inletProfileJetsAll (lam : ℂ) (q : Planar.Profile) (hq : Planar.IsGrowingEigenpair lam q)
    (dm dp : ℝ) (hdm : 0 < dm) :
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ 1 → p.mode = q →
      ∀ (i : Fin 2) (K : ℕ), ∃ M κ : ℝ, 0 ≤ M ∧ 0 < κ ∧
        ContDiff ℝ ∞ (p.inletProfile i) ∧
        (∀ x : ℝ × (ℝ × ℝ), p.H / 2 < x.1 → p.inletProfile i x = 0) ∧
        ∀ l : ℕ, l ≤ K → ∀ x : ℝ × (ℝ × ℝ),
          ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ ≤ M * Real.exp (-(κ * |x.2.2|)) := by
  intro p d hreg hν hmode i K
  obtain ⟨C3, κ0, N, hC3, hκ0, h3'⟩ := UnforcedLeray.Short.IIb.cutStreamJets lam q hq (K + 1)
  obtain ⟨C4, hC4, h4'⟩ := UnforcedLeray.Short.IIb.ringStreamJetsDecay K
  have hνpos : 0 < p.ν := p.ν_pos
  have hc1 : 1 ≤ p.c := by
    rw [hreg.c_eq, one_le_inv₀ (by positivity)]
    nlinarith
  have hcpos : 0 < p.c := by linarith
  have hR1 : 1 ≤ p.R := by
    have hε : p.ε ≤ 1 := by
      rw [hreg.eps_eq]
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ d / p.ν := div_nonneg (by linarith [hreg.dm_pos, hreg.dm_le]) hνpos.le
      rw [neg_div]; linarith
    show 1 ≤ p.ε⁻¹
    exact one_le_inv₀ p.ε_pos |>.mpr hε
  have hH : 0 < p.H := p.H_pos
  have hHi : 0 ≤ p.H⁻¹ := inv_nonneg.2 hH.le
  obtain ⟨hcutsm, hcut⟩ := h3' p hmode hc1 hH i
  have hM0 : 0 ≤ C3 * (1 + p.H⁻¹) ^ (K + 1) * p.c ^ N :=
    mul_nonneg (mul_nonneg hC3.le (pow_nonneg (by linarith) (K + 1))) (pow_nonneg hcpos.le N)
  have hring := h4' p.R (p.H / 2) p.c κ0 (C3 * (1 + p.H⁻¹) ^ (K + 1) * p.c ^ N) (p.cutStream i)
    hR1 (half_pos hH) hcpos hκ0 hM0 hcutsm
    (fun x hx => by
      unfold Params.cutStream
      simp [UnforcedLeray.Cons.C03.Concrete.ageCutoff_eq_zero hH (show p.H / 2 ≤ x.1 from hx.le)])
    (fun x hx => UnforcedLeray.Short.IIb.cutStreamSVanish lam q hq p hmode hc1 hH i x hx)
    (fun l hl x => hcut l hl x)
  have hκpos : 0 < κ0 / (2 * p.c) := div_pos hκ0 (by linarith)
  refine ⟨C4 * (1 + p.H / 2) * (1 + p.c / κ0) * (C3 * (1 + p.H⁻¹) ^ (K + 1) * p.c ^ N),
    κ0 / (2 * p.c), ?_, hκpos, ?_, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (mul_nonneg hC4.le (by linarith))
      (add_nonneg zero_le_one (div_nonneg hcpos.le hκ0.le))) hM0
  · unfold Params.inletProfile
    exact UnforcedLeray.Short.IIb.inletCD_ringStreamProfile hcutsm
  · intro x hx
    have hcut0 : p.cutStream i x = 0 := by
      unfold Params.cutStream
      simp [UnforcedLeray.Cons.C03.Concrete.ageCutoff_eq_zero hH hx.le]
    have hev : ∀ᶠ y in 𝓝 x, p.H / 2 < y.1 :=
      (continuous_fst.tendsto x).eventually (lt_mem_nhds hx)
    have hfun : p.cutStream i =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [hev] with y hy
      unfold Params.cutStream
      simp [UnforcedLeray.Cons.C03.Concrete.ageCutoff_eq_zero hH hy.le]
    have hfd : fderiv ℝ (p.cutStream i) x = 0 := by
      rw [hfun.fderiv_eq]; simp
    have hdS : Axi.dS (p.cutStream i) x = 0 := by unfold Axi.dS; rw [hfd]; simp
    have hdQ : Axi.dQ (p.cutStream i) x = 0 := by unfold Axi.dQ; rw [hfd]; simp
    have hdE : Axi.dEta (p.cutStream i) x = 0 := by unfold Axi.dEta; rw [hfd]; simp
    simp [Params.inletProfile, Axi.ringStreamProfile, hdS, hdQ, hdE, hcut0]
  · intro l hl x
    have hmain := hring l (by omega) x
    rw [show -((κ0 / 2) * |x.2.2| / p.c) = -((κ0 / (2 * p.c)) * |x.2.2|) by ring] at hmain
    exact hmain

/-- All-order shell jets for `realC (Nv R b τ ·)` and its `∂_τ`. -/
private theorem nvShellJetsAll (R ρ0 R0 κ M : ℝ) (hR : 0 < R) (hρ0 : 0 < ρ0) (hκ : 0 < κ)
    (hM : 0 ≤ M) (K : ℕ) (b : ℝ × (ℝ × ℝ) → Axi.Merid) (hb : ContDiff ℝ ∞ b)
    (hj : ∀ l : ℕ, l ≤ K + 1 → ∀ m : ℝ × (ℝ × ℝ),
      ‖iteratedFDeriv ℝ l b m‖ ≤ M * Real.exp (-(κ * |m.2.2|))) (N : ℕ) :
    ∃ C : ℝ, ∀ τ : ℝ, ∀ y : UnforcedLeray.Space, ρ0 ≤ Axi.ϱ y → Axi.ϱ y ≤ R0 →
      (∀ k : ℕ, k ≤ K →
        ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space => realC (Axi.Nv R b τ x)) y‖ ≤
          C * (1 + |y 2|) ^ (-(N : ℝ))) ∧
      (∀ k : ℕ, k ≤ K →
        ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space =>
          UnforcedLeray.PhaseSpace.dτ
            (fun q : ℝ × UnforcedLeray.Space => realC (Axi.Nv R b q.1 q.2)) (τ, x)) y‖ ≤
          C * (1 + |y 2|) ^ (-(N : ℝ))) := by
  obtain ⟨C1, hC1⟩ := Shell.shellLiftJets_of Shell.shellFrameJets Shell.shellAgeJets
    Shell.shellPhaseJets Shell.shellTransJets Shell.shellAbsorb hR hρ0 hκ hM K hb
    (fun l hl m => hj l (by omega) m) N
  have hb's : ContDiff ℝ ∞ (fun m => (R / 2) • Axi.dQ b m) :=
    (Shell.contDiff_dQ hb).const_smul (R / 2)
  have hj' : ∀ l : ℕ, l ≤ K → ∀ m : ℝ × (ℝ × ℝ),
      ‖iteratedFDeriv ℝ l (fun m => (R / 2) • Axi.dQ b m) m‖ ≤
        (R / 2 * M) * Real.exp (-(κ * |m.2.2|)) := by
    intro l hl m
    have h1 : iteratedFDeriv ℝ l (fun m => (R / 2) • Axi.dQ b m) m =
        (R / 2) • iteratedFDeriv ℝ l (Axi.dQ b) m :=
      iteratedFDeriv_const_smul_apply'
        ((Shell.contDiff_dQ hb).contDiffAt.of_le (by simp))
    rw [h1, norm_smul, Real.norm_of_nonneg (by positivity), mul_assoc]
    exact mul_le_mul_of_nonneg_left
      ((Shell.norm_iteratedFDeriv_dQ_le hb l m).trans (hj (l + 1) (by omega) m)) (by positivity)
  obtain ⟨C2, hC2⟩ := Shell.shellLiftJets_of Shell.shellFrameJets Shell.shellAgeJets
    Shell.shellPhaseJets Shell.shellTransJets Shell.shellAbsorb hR hρ0 hκ (by positivity) K hb's hj' N
  refine ⟨max C1 C2, fun τ y hy1 hy2 => ⟨fun k hk => ?_, fun k hk => ?_⟩⟩
  · have hp : 0 ≤ (1 + |y 2|) ^ (-(N : ℝ)) := by positivity
    exact (hC1 τ y hy1 hy2 k hk).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp)
  · have hp : 0 ≤ (1 + |y 2|) ^ (-(N : ℝ)) := by positivity
    have hax := Shell.notMem_axis_of_le hρ0 hy1
    have hev : (fun x : UnforcedLeray.Space => UnforcedLeray.PhaseSpace.dτ
          (fun q : ℝ × UnforcedLeray.Space => realC (Nv R b q.1 q.2)) (τ, x)) =ᶠ[nhds y]
        (fun x => realC (Nv R (fun m => (R / 2) • Axi.dQ b m) τ x)) := by
      filter_upwards [isOpen_compl_axis.mem_nhds hax] with x hx
      exact Shell.shellDτ R b hR hb τ x hx
    rw [(hev.iteratedFDeriv ℝ k).eq_of_nhds]
    exact (hC2 τ y hy1 hy2 k hk).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hp)

/-- All-order near-axis decay of `p.Efun i` and `dτ (p.Efun i)` on `ϱ y ≤ R0`, with `ν₀ = 1`. -/
theorem inletENearJetsAll (lam : ℂ) (q : Planar.Profile) (hq : Planar.IsGrowingEigenpair lam q)
    (dm dp : ℝ) (hdm : 0 < dm) :
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ 1 → p.mode = q →
      ∀ (i : Fin 2) (K N : ℕ) (R0 : ℝ), 0 < R0 → ∃ C : ℝ,
        ∀ (τ : ℝ) (y : UnforcedLeray.Space), Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ≤ R0 →
          (∀ k : ℕ, k ≤ K →
            ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y‖ ≤
              C * (1 + |y 2|) ^ (-(N : ℝ))) ∧
          (∀ k : ℕ, k ≤ K →
            ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space =>
              UnforcedLeray.PhaseSpace.dτ (p.Efun i) (τ, x)) y‖ ≤
              C * (1 + |y 2|) ^ (-(N : ℝ))) := by
  intro p d hreg hν hmode i K N R0 _hR0
  obtain ⟨M, κ, hM, hκ, hsm, hvan, hj⟩ :=
    inletProfileJetsAll lam q hq dm dp hdm p d hreg hν hmode i (K + 1)
  have hS : 0 < p.H / 2 := half_pos p.H_pos
  have hsq : 0 < Real.sqrt (p.H / 2) := Real.sqrt_pos.2 hS
  have hρ : 0 < p.R / Real.sqrt (p.H / 2) := div_pos p.R_pos hsq
  obtain ⟨C, hC⟩ := nvShellJetsAll p.R (p.R / Real.sqrt (p.H / 2)) R0 κ M p.R_pos hρ hκ hM K
    (p.inletProfile i) hsm hj N
  refine ⟨max C 0, fun τ y hy => ?_⟩
  change Axi.ϱ y ≤ R0 at hy
  by_cases hshell : p.R / Real.sqrt (p.H / 2) ≤ Axi.ϱ y
  · obtain ⟨h1, h2⟩ := hC τ y hshell hy
    have hp : 0 < (1 + |y 2|) ^ (-(N : ℝ)) := by positivity
    exact ⟨fun k hk => (h1 k hk).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp.le),
      fun k hk => (h2 k hk).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp.le)⟩
  · push_neg at hshell
    have hp : 0 ≤ max C 0 * (1 + |y 2|) ^ (-(N : ℝ)) := by positivity
    have hcont : Continuous (fun x : UnforcedLeray.Space => Axi.ϱ x) := by
      unfold Axi.ϱ; fun_prop
    have hopen : IsOpen {x : UnforcedLeray.Space | Axi.ϱ x < p.R / Real.sqrt (p.H / 2)} :=
      isOpen_lt hcont continuous_const
    have hnhds : {x : UnforcedLeray.Space | Axi.ϱ x < p.R / Real.sqrt (p.H / 2)} ∈ nhds y :=
      hopen.mem_nhds hshell
    have hz : ∀ x ∈ {x : UnforcedLeray.Space | Axi.ϱ x < p.R / Real.sqrt (p.H / 2)},
        p.Efun i (τ, x) = 0 := fun x hx => by
      change realC (Axi.Nv p.R (p.inletProfile i) τ x) = 0
      rw [Nv_eq_zero_of_lt p.R_pos hS hvan τ hx]; simp [realC]
    have hev : (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) =ᶠ[nhds y]
        fun _ => (0 : UnforcedLeray.PhaseSpace.CVec3) :=
      Filter.eventually_of_mem hnhds hz
    refine ⟨fun k _ => ?_, fun k _ => ?_⟩
    · rw [(hev.iteratedFDeriv ℝ k).self_of_nhds]
      have : iteratedFDeriv ℝ k (fun _ : UnforcedLeray.Space =>
          (0 : UnforcedLeray.PhaseSpace.CVec3)) y = 0 := by simp
      rw [this]; simpa using hp
    · have hev2 : (fun x : UnforcedLeray.Space =>
          UnforcedLeray.PhaseSpace.dτ (p.Efun i) (τ, x)) =ᶠ[nhds y]
          fun _ => (0 : UnforcedLeray.PhaseSpace.CVec3) := by
        filter_upwards [hopen.mem_nhds hshell] with x hx
        have hnb : {q : ℝ × UnforcedLeray.Space | Axi.ϱ q.2 < p.R / Real.sqrt (p.H / 2)} ∈
            nhds (τ, x) :=
          (isOpen_lt (hcont.comp continuous_snd) continuous_const).mem_nhds hx
        have hq' : (fun q : ℝ × UnforcedLeray.Space => p.Efun i (q.1, q.2)) =ᶠ[nhds (τ, x)]
            fun _ => (0 : UnforcedLeray.PhaseSpace.CVec3) :=
          Filter.eventually_of_mem hnb (fun q hq => by
            change realC (Axi.Nv p.R (p.inletProfile i) q.1 q.2) = 0
            rw [Nv_eq_zero_of_lt p.R_pos hS hvan q.1 hq]; simp [realC])
        simp [UnforcedLeray.PhaseSpace.dτ, hq'.fderiv_eq]
      rw [(hev2.iteratedFDeriv ℝ k).self_of_nhds]
      have : iteratedFDeriv ℝ k (fun _ : UnforcedLeray.Space =>
          (0 : UnforcedLeray.PhaseSpace.CVec3)) y = 0 := by simp
      rw [this]; simpa using hp

/-! ### All-order spatial derivative bound on `Jets.Sfun` -/

section SfunAll

open UnforcedLeray.PhaseSpace Jets

/-- Continuous bilinear map `(s, v) ↦ s • v` from `ℝ × CVec3` to `CVec3`. -/
def smulCVecBilin : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3 :=
  ContinuousLinearMap.lsmul ℝ ℝ

/-- Continuous bilinear map `(z, v) ↦ z • v` from `ℂ × CVec3` to `CVec3`. -/
def cvecSmulBilin : ℂ →L[ℝ] CVec3 →L[ℝ] CVec3 :=
  (LinearMap.mk₂ ℝ (fun (z : ℂ) (v : CVec3) => z • v)
    add_smul (fun c z v => by rw [smul_assoc])
    smul_add (fun c z v => by rw [smul_comm])).mkContinuous₂ 1
    (fun z v => by rw [one_mul]; change ‖z • v‖ ≤ ‖z‖ * ‖v‖; exact (norm_smul z v).le)

/-- `realC` as a continuous `ℝ`-linear map `Space →L[ℝ] CVec3`. -/
def realCCLM : Space →L[ℝ] CVec3 :=
  { toFun := realC
    map_add' := fun x y => by ext i; simp [realC_apply]
    map_smul' := fun c x => by ext i; simp [realC_apply]
    cont := UnforcedLeray.Short.PartIIIb.Concrete.contDiff_realC_meas.continuous }

lemma norm_realCCLM_le_one : ‖realCCLM‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
    change ‖realC x‖ ≤ 1 * ‖x‖
    have hnorm : ‖realC x‖ = ‖x‖ := by
      rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.norm_sq_eq,
        EuclideanSpace.norm_sq_eq]
      simp [realC_apply, Real.norm_eq_abs, Complex.norm_real]
    linarith)

lemma norm_projR_le_one (k : Fin 3) : ‖(EuclideanSpace.proj k : Space →L[ℝ] ℝ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
    simpa using PiLp.norm_apply_le x k)

lemma norm_projC_le_one (k : Fin 3) :
    ‖((EuclideanSpace.proj k : CVec3 →L[ℂ] ℂ).restrictScalars ℝ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
    simpa using PiLp.norm_apply_le x k)

/-- Helper: `‖iteratedFDeriv ℝ m (fun x => fderiv ℝ f x v) y‖ ≤ ‖iteratedFDeriv ℝ (m + 1) f y‖ * ‖v‖`. -/
lemma norm_iteratedFDeriv_fderiv_apply_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : ContDiff ℝ ∞ f)
    (v : E) (m : ℕ) (y : E) :
    ‖iteratedFDeriv ℝ m (fun x => fderiv ℝ f x v) y‖ ≤ ‖iteratedFDeriv ℝ (m + 1) f y‖ * ‖v‖ := by
  have h1 : (fun x => fderiv ℝ f x v) = fun x => (ContinuousLinearMap.apply ℝ F v) (fderiv ℝ f x) := rfl
  rw [h1]
  have hf1 : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hle := ContinuousLinearMap.norm_iteratedFDeriv_comp_left (ContinuousLinearMap.apply ℝ F v)
    (hf1.contDiffAt) (by simp : (m : WithTop ℕ∞) ≤ ∞) (x := y)
  have happ : ‖ContinuousLinearMap.apply ℝ F v‖ ≤ ‖v‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) (fun L => by
      simpa [mul_comm] using L.le_opNorm v)
  have hfd : ‖iteratedFDeriv ℝ m (fderiv ℝ f) y‖ = ‖iteratedFDeriv ℝ (m + 1) f y‖ := by
    rw [norm_iteratedFDeriv_fderiv]
  calc ‖iteratedFDeriv ℝ m (fun x => (ContinuousLinearMap.apply ℝ F v) (fderiv ℝ f x)) y‖
      ≤ ‖ContinuousLinearMap.apply ℝ F v‖ * ‖iteratedFDeriv ℝ m (fderiv ℝ f) y‖ := hle
    _ = ‖ContinuousLinearMap.apply ℝ F v‖ * ‖iteratedFDeriv ℝ (m + 1) f y‖ := by rw [hfd]
    _ ≤ ‖v‖ * ‖iteratedFDeriv ℝ (m + 1) f y‖ :=
        mul_le_mul_of_nonneg_right happ (norm_nonneg (iteratedFDeriv ℝ (m + 1) f y))
    _ = ‖iteratedFDeriv ℝ (m + 1) f y‖ * ‖v‖ := mul_comm _ _

/-- Helper: `‖iteratedFDeriv ℝ m (fun x => x k) y‖ ≤ 1 + ‖y‖`. -/
lemma norm_iteratedFDeriv_coord_le (k : Fin 3) (m : ℕ) (y : Space) :
    ‖iteratedFDeriv ℝ m (fun x : Space => x k) y‖ ≤ 1 + ‖y‖ := by
  have hclm : (fun x : Space => x k) = (EuclideanSpace.proj k : Space →L[ℝ] ℝ) := rfl
  rcases m with _ | _ | m
  · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    exact (PiLp.norm_apply_le y k).trans (by linarith)
  · rw [hclm, norm_iteratedFDeriv_one, ContinuousLinearMap.fderiv]
    exact (norm_projR_le_one k).trans (by linarith [norm_nonneg y])
  · rw [hclm, ← norm_iteratedFDeriv_fderiv]
    have hfd : fderiv ℝ (EuclideanSpace.proj k : Space →L[ℝ] ℝ) = fun _ =>
        (EuclideanSpace.proj k : Space →L[ℝ] ℝ) := by
      ext1 z; exact (EuclideanSpace.proj k : Space →L[ℝ] ℝ).fderiv
    rw [hfd, iteratedFDeriv_const_of_ne (Nat.succ_ne_zero m)]
    simp; positivity

lemma norm_ek_le_one (k : Fin 3) : ‖ek k‖ ≤ 1 := by
  rw [← sq_le_sq₀ (norm_nonneg _) zero_le_one, EuclideanSpace.norm_sq_eq]
  simp [ek, EuclideanSpace.single]

/-- Universal constant (depending only on `m`) in `norm_iteratedFDeriv_Sfun_le`. -/
def sfunConst (m : ℕ) : ℝ :=
  6 * max 1 (max (2 * (‖smulCVecBilin‖ * 2 ^ m * ((m : ℝ) + 1)))
    (2 ^ m * ((m : ℝ) + 1) * (3 * (‖smulCVecBilin‖ + ‖cvecSmulBilin‖)) + 3))

lemma sfunConst_nonneg (m : ℕ) : 0 ≤ sfunConst m := by
  unfold sfunConst; positivity

/-- All-order spatial derivative bound on `Jets.Sfun` in terms of `1 + ‖y‖`, `|ν|`, and the
slice jets of `r`, `e`, `d`, with universal constant `sfunConst m`. -/
theorem norm_iteratedFDeriv_Sfun_le (e d : Space → CVec3) (r : Space → Space) (ν : ℝ)
    (he : ContDiff ℝ ∞ e) (hd : ContDiff ℝ ∞ d) (hr : ContDiff ℝ ∞ r) (m : ℕ) (y : Space) :
    ‖iteratedFDeriv ℝ m (Sfun e d r ν) y‖ ≤
      sfunConst m * (1 + |ν|) * (1 + ‖y‖) *
        (1 + ∑ k ∈ Finset.range (m + 2), ‖iteratedFDeriv ℝ k r y‖) *
        ((∑ k ∈ Finset.range (m + 3), ‖iteratedFDeriv ℝ k e y‖) +
          ‖iteratedFDeriv ℝ m d y‖) := by
  let Bsum : ℝ := 3 * (‖smulCVecBilin‖ + ‖cvecSmulBilin‖)
  let C0 : ℝ := 2 * (‖smulCVecBilin‖ * 2 ^ m * ((m : ℝ) + 1))
  let K : ℝ := sfunConst m
  have hK0 : 0 ≤ K := sfunConst_nonneg m
  set Rsum := ∑ k ∈ Finset.range (m + 2), ‖iteratedFDeriv ℝ k r y‖
  set Esum := ∑ k ∈ Finset.range (m + 3), ‖iteratedFDeriv ℝ k e y‖
  set Dnorm := ‖iteratedFDeriv ℝ m d y‖
  have hR0 : 0 ≤ Rsum := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hE0 : 0 ≤ Esum := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hD0 : 0 ≤ Dnorm := norm_nonneg _
  have hRle : ∀ k, k ≤ m + 1 → ‖iteratedFDeriv ℝ k r y‖ ≤ Rsum := fun k hk =>
    Finset.single_le_sum (f := fun j => ‖iteratedFDeriv ℝ j r y‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
  have hEle : ∀ k, k ≤ m + 2 → ‖iteratedFDeriv ℝ k e y‖ ≤ Esum := fun k hk =>
    Finset.single_le_sum (f := fun j => ‖iteratedFDeriv ℝ j e y‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
  have hcd_e1 : ∀ k : Fin 3, ContDiff ℝ ∞ (fun x => fderiv ℝ e x (ek k)) := fun k =>
    (ContinuousLinearMap.apply ℝ CVec3 (ek k)).contDiff.comp (he.fderiv_right (by simp))
  have hcd_e2 : ∀ k : Fin 3, ContDiff ℝ ∞ (fun x => fderiv ℝ (fun z => fderiv ℝ e z (ek k)) x (ek k)) :=
    fun k => (ContinuousLinearMap.apply ℝ CVec3 (ek k)).contDiff.comp ((hcd_e1 k).fderiv_right (by simp))
  have hcd_rk : ∀ k : Fin 3, ContDiff ℝ ∞ (fun x => r x k) := fun k =>
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff.comp hr
  have hcd_ek : ∀ k : Fin 3, ContDiff ℝ ∞ (fun x => e x k) := fun k =>
    ((EuclideanSpace.proj k : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp he
  have hcd_rk' : ∀ k : Fin 3, ContDiff ℝ ∞ (fun x => realC (fderiv ℝ r x (ek k))) := fun k =>
    realCCLM.contDiff.comp
      ((ContinuousLinearMap.apply ℝ Space (ek k)).contDiff.comp (hr.fderiv_right (by simp)))
  have hcd_rad : ContDiff ℝ ∞ (fun x : Space => ∑ k : Fin 3, (x k) • fderiv ℝ e x (ek k)) :=
    ContDiff.sum fun k _ => ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff).smul (hcd_e1 k)
  have hcd_lap : ContDiff ℝ ∞ (fun x : Space => ∑ k : Fin 3, fderiv ℝ (fun z => fderiv ℝ e z (ek k)) x (ek k)) :=
    ContDiff.sum fun k _ => hcd_e2 k
  have hcd_adv : ContDiff ℝ ∞ (fun x : Space => ∑ k : Fin 3, ((r x k : ℝ) : ℂ) • fderiv ℝ e x (ek k)) :=
    ContDiff.sum fun k _ => by
      have heq : (fun x : Space => ((r x k : ℝ) : ℂ) • fderiv ℝ e x (ek k)) =
          fun x => smulCVecBilin (r x k) (fderiv ℝ e x (ek k)) := by
        funext x; ext j; simp [smulCVecBilin]
      rw [heq]
      exact smulCVecBilin.isBoundedBilinearMap.contDiff.comp ((hcd_rk k).prodMk (hcd_e1 k))
  have hcd_grad : ContDiff ℝ ∞ (fun x : Space => ∑ k : Fin 3, e x k • realC (fderiv ℝ r x (ek k))) :=
    ContDiff.sum fun k _ => cvecSmulBilin.isBoundedBilinearMap.contDiff.comp ((hcd_ek k).prodMk (hcd_rk' k))
  have hm_top : (m : WithTop ℕ∞) ≤ ∞ := by simp
  -- Decompose `Sfun` at `y` using `iteratedFDeriv_add/sub/smul`
  have hS_eq : Sfun e d r ν =
      (fun x : Space =>
        ((((d x - (1 / 2 : ℝ) • ∑ k : Fin 3, (x k) • fderiv ℝ e x (ek k))
          - ν • ∑ k : Fin 3, fderiv ℝ (fun z => fderiv ℝ e z (ek k)) x (ek k))
          - (1 / 2 : ℝ) • e x)
          + ∑ k : Fin 3, ((r x k : ℝ) : ℂ) • fderiv ℝ e x (ek k))
          + ∑ k : Fin 3, e x k • realC (fderiv ℝ r x (ek k))) := rfl
  have h1 := (hd.sub (hcd_rad.const_smul (1 / 2 : ℝ))).contDiffAt (x := y)
  have h2 := h1.sub ((hcd_lap.const_smul ν).contDiffAt (x := y))
  have h3 := h2.sub ((he.const_smul (1 / 2 : ℝ)).contDiffAt (x := y))
  have h4 := h3.add (hcd_adv.contDiffAt (x := y))
  rw [hS_eq]
  erw [iteratedFDeriv_add_apply (h4.of_le hm_top) ((hcd_grad.contDiffAt (x := y)).of_le hm_top),
    iteratedFDeriv_add_apply (h3.of_le hm_top) ((hcd_adv.contDiffAt (x := y)).of_le hm_top),
    iteratedFDeriv_sub_apply (h2.of_le hm_top) (((he.const_smul (1 / 2 : ℝ)).contDiffAt (x := y)).of_le hm_top),
    iteratedFDeriv_sub_apply (h1.of_le hm_top) (((hcd_lap.const_smul ν).contDiffAt (x := y)).of_le hm_top),
    iteratedFDeriv_sub_apply ((hd.contDiffAt (x := y)).of_le hm_top) (((hcd_rad.const_smul (1 / 2 : ℝ)).contDiffAt (x := y)).of_le hm_top),
    iteratedFDeriv_const_smul_apply' ((hcd_rad.contDiffAt (x := y)).of_le hm_top),
    iteratedFDeriv_const_smul_apply' ((hcd_lap.contDiffAt (x := y)).of_le hm_top),
    iteratedFDeriv_const_smul_apply' ((he.contDiffAt (x := y)).of_le hm_top)]
  -- Bound each of the 6 terms
  have ht1 : ‖iteratedFDeriv ℝ m d y‖ ≤ Dnorm := le_rfl
  have ht2 : ‖(1 / 2 : ℝ) • iteratedFDeriv ℝ m (fun x : Space => ∑ k : Fin 3, (x k) • fderiv ℝ e x (ek k)) y‖ ≤
      (1 / 2 : ℝ) * (3 * (‖smulCVecBilin‖ * 2 ^ m * ((m : ℝ) + 1) * (1 + ‖y‖) * Esum)) := by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    have hsum : iteratedFDeriv ℝ m (fun x : Space => ∑ k : Fin 3, (x k) • fderiv ℝ e x (ek k)) =
        ∑ k : Fin 3, iteratedFDeriv ℝ m (fun x : Space => (x k) • fderiv ℝ e x (ek k)) :=
      iteratedFDeriv_sum (fun k _ => ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff.smul (hcd_e1 k)).of_le hm_top)
    rw [hsum, Finset.sum_apply]
    refine (norm_sum_le _ _).trans (sum3_le _ _ fun k => ?_)
    have hsm := smulCVecBilin.norm_iteratedFDeriv_le_of_bilinear
      (EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff (hcd_e1 k) y hm_top
    refine hsm.trans ?_
    have hsum_le : ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun x : Space => x k) y‖ *
        ‖iteratedFDeriv ℝ (m - i) (fun x => fderiv ℝ e x (ek k)) y‖ ≤
        2 ^ m * ((m : ℝ) + 1) * ((1 + ‖y‖) * Esum) := by
      have hterm : ∀ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun x : Space => x k) y‖ *
          ‖iteratedFDeriv ℝ (m - i) (fun x => fderiv ℝ e x (ek k)) y‖ ≤
          2 ^ m * ((1 + ‖y‖) * Esum) := fun i hi => by
        have him : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        have hch : (m.choose i : ℝ) ≤ 2 ^ m := by exact_mod_cast Nat.choose_le_two_pow m i
        have hc := norm_iteratedFDeriv_coord_le k i y
        have he' : ‖iteratedFDeriv ℝ (m - i) (fun x => fderiv ℝ e x (ek k)) y‖ ≤ Esum := by
          refine (norm_iteratedFDeriv_fderiv_apply_le he (ek k) (m - i) y).trans ?_
          have hmi : m - i + 1 ≤ m + 2 := by omega
          calc ‖iteratedFDeriv ℝ (m - i + 1) e y‖ * ‖ek k‖
              ≤ Esum * 1 := mul_le_mul (hEle (m - i + 1) hmi) (norm_ek_le_one k) (norm_nonneg _) hE0
            _ = Esum := mul_one _
        calc (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun x : Space => x k) y‖ *
              ‖iteratedFDeriv ℝ (m - i) (fun x => fderiv ℝ e x (ek k)) y‖
            ≤ (2 ^ m * (1 + ‖y‖)) * Esum :=
              mul_le_mul (mul_le_mul hch hc (norm_nonneg _) (by positivity)) he' (norm_nonneg _) (by positivity)
          _ = 2 ^ m * ((1 + ‖y‖) * Esum) := by ring
      calc ∑ i ∈ Finset.range (m + 1), _ ≤ ∑ _i ∈ Finset.range (m + 1), 2 ^ m * ((1 + ‖y‖) * Esum) :=
            Finset.sum_le_sum hterm
        _ = ((m : ℝ) + 1) * (2 ^ m * ((1 + ‖y‖) * Esum)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
        _ = 2 ^ m * ((m : ℝ) + 1) * ((1 + ‖y‖) * Esum) := by ring
    calc ‖smulCVecBilin‖ * ∑ i ∈ Finset.range (m + 1), _
        ≤ ‖smulCVecBilin‖ * (2 ^ m * ((m : ℝ) + 1) * ((1 + ‖y‖) * Esum)) :=
          mul_le_mul_of_nonneg_left hsum_le (norm_nonneg smulCVecBilin)
      _ = ‖smulCVecBilin‖ * 2 ^ m * ((m : ℝ) + 1) * (1 + ‖y‖) * Esum := by ring
  have ht3 : ‖ν • iteratedFDeriv ℝ m (fun x : Space => ∑ k : Fin 3, fderiv ℝ (fun z => fderiv ℝ e z (ek k)) x (ek k)) y‖ ≤
      |ν| * (3 * Esum) := by
    rw [norm_smul, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [iteratedFDeriv_sum (fun k _ => (hcd_e2 k).of_le hm_top), Finset.sum_apply]
    refine (norm_sum_le _ _).trans (sum3_le _ _ fun k => ?_)
    have h1 := norm_iteratedFDeriv_fderiv_apply_le (hcd_e1 k) (ek k) m y
    have h2 : ‖iteratedFDeriv ℝ (m + 1) (fun z => fderiv ℝ e z (ek k)) y‖ ≤ Esum := by
      refine (norm_iteratedFDeriv_fderiv_apply_le he (ek k) (m + 1) y).trans ?_
      calc ‖iteratedFDeriv ℝ (m + 2) e y‖ * ‖ek k‖
          ≤ Esum * 1 := mul_le_mul (hEle _ (by omega)) (norm_ek_le_one k) (norm_nonneg _) hE0
        _ = Esum := mul_one _
    calc ‖iteratedFDeriv ℝ m (fun x => fderiv ℝ (fun z => fderiv ℝ e z (ek k)) x (ek k)) y‖
        ≤ ‖iteratedFDeriv ℝ (m + 1) (fun z => fderiv ℝ e z (ek k)) y‖ * ‖ek k‖ := h1
      _ ≤ Esum * 1 := mul_le_mul h2 (norm_ek_le_one k) (norm_nonneg _) hE0
      _ = Esum := mul_one _
  have ht4 : ‖(1 / 2 : ℝ) • iteratedFDeriv ℝ m e y‖ ≤ (1 / 2 : ℝ) * Esum := by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
    exact mul_le_mul_of_nonneg_left (hEle m (by omega)) (by norm_num)
  have ht5 : ‖iteratedFDeriv ℝ m (fun x : Space => ∑ k : Fin 3, ((r x k : ℝ) : ℂ) • fderiv ℝ e x (ek k)) y‖ ≤
      3 * (2 ^ m * ((m : ℝ) + 1) * ‖smulCVecBilin‖ * Rsum * Esum) := by
    rw [show (fun x : Space => ∑ k : Fin 3, ((r x k : ℝ) : ℂ) • fderiv ℝ e x (ek k)) =
        fun x : Space => ∑ k : Fin 3, smulCVecBilin (r x k) (fderiv ℝ e x (ek k)) from by
          ext x j; simp [smulCVecBilin]]
    have hsum : iteratedFDeriv ℝ m (fun x : Space => ∑ k : Fin 3, smulCVecBilin (r x k) (fderiv ℝ e x (ek k))) =
        ∑ k : Fin 3, iteratedFDeriv ℝ m (fun x : Space => smulCVecBilin (r x k) (fderiv ℝ e x (ek k))) :=
      iteratedFDeriv_sum (fun k _ => (smulCVecBilin.isBoundedBilinearMap.contDiff.comp ((hcd_rk k).prodMk (hcd_e1 k))).of_le hm_top)
    rw [hsum, Finset.sum_apply]
    refine (norm_sum_le _ _).trans (sum3_le _ _ fun k => ?_)
    refine (smulCVecBilin.norm_iteratedFDeriv_le_of_bilinear (hcd_rk k) (hcd_e1 k) y hm_top).trans ?_
    have hsum_le : ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun x => r x k) y‖ *
        ‖iteratedFDeriv ℝ (m - i) (fun x => fderiv ℝ e x (ek k)) y‖ ≤
        2 ^ m * ((m : ℝ) + 1) * (Rsum * Esum) := by
      have hterm : ∀ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun x => r x k) y‖ *
          ‖iteratedFDeriv ℝ (m - i) (fun x => fderiv ℝ e x (ek k)) y‖ ≤
          2 ^ m * (Rsum * Esum) := fun i hi => by
        have him : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        have hch : (m.choose i : ℝ) ≤ 2 ^ m := by exact_mod_cast Nat.choose_le_two_pow m i
        have hr' : ‖iteratedFDeriv ℝ i (fun x => r x k) y‖ ≤ Rsum := by
          have hcomp := ContinuousLinearMap.norm_iteratedFDeriv_comp_left
            (EuclideanSpace.proj k : Space →L[ℝ] ℝ) hr.contDiffAt (by simp : (i : WithTop ℕ∞) ≤ ∞) (x := y)
          refine hcomp.trans ?_
          calc ‖(EuclideanSpace.proj k : Space →L[ℝ] ℝ)‖ * ‖iteratedFDeriv ℝ i r y‖
              ≤ 1 * Rsum := mul_le_mul (norm_projR_le_one k) (hRle i (by omega)) (norm_nonneg _) zero_le_one
            _ = Rsum := one_mul _
        have he' : ‖iteratedFDeriv ℝ (m - i) (fun x => fderiv ℝ e x (ek k)) y‖ ≤ Esum := by
          refine (norm_iteratedFDeriv_fderiv_apply_le he (ek k) (m - i) y).trans ?_
          have hmi : m - i + 1 ≤ m + 2 := by omega
          calc ‖iteratedFDeriv ℝ (m - i + 1) e y‖ * ‖ek k‖
              ≤ Esum * 1 := mul_le_mul (hEle (m - i + 1) hmi) (norm_ek_le_one k) (norm_nonneg _) hE0
            _ = Esum := mul_one _
        calc (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun x => r x k) y‖ *
              ‖iteratedFDeriv ℝ (m - i) (fun x => fderiv ℝ e x (ek k)) y‖
            ≤ (2 ^ m * Rsum) * Esum :=
              mul_le_mul (mul_le_mul hch hr' (norm_nonneg _) (by positivity)) he' (norm_nonneg _) (by positivity)
          _ = 2 ^ m * (Rsum * Esum) := by ring
      calc ∑ i ∈ Finset.range (m + 1), _ ≤ ∑ _i ∈ Finset.range (m + 1), 2 ^ m * (Rsum * Esum) :=
            Finset.sum_le_sum hterm
        _ = 2 ^ m * ((m : ℝ) + 1) * (Rsum * Esum) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    calc ‖smulCVecBilin‖ * ∑ i ∈ Finset.range (m + 1), _
        ≤ ‖smulCVecBilin‖ * (2 ^ m * ((m : ℝ) + 1) * (Rsum * Esum)) :=
          mul_le_mul_of_nonneg_left hsum_le (norm_nonneg smulCVecBilin)
      _ = 2 ^ m * ((m : ℝ) + 1) * ‖smulCVecBilin‖ * Rsum * Esum := by ring
  have ht6 : ‖iteratedFDeriv ℝ m (fun x : Space => ∑ k : Fin 3, e x k • realC (fderiv ℝ r x (ek k))) y‖ ≤
      3 * (2 ^ m * ((m : ℝ) + 1) * ‖cvecSmulBilin‖ * Esum * Rsum) := by
    rw [show (fun x : Space => ∑ k : Fin 3, e x k • realC (fderiv ℝ r x (ek k))) =
        fun x : Space => ∑ k : Fin 3, cvecSmulBilin (e x k) (realC (fderiv ℝ r x (ek k))) from rfl]
    have hsum : iteratedFDeriv ℝ m (fun x : Space => ∑ k : Fin 3, cvecSmulBilin (e x k) (realC (fderiv ℝ r x (ek k)))) =
        ∑ k : Fin 3, iteratedFDeriv ℝ m (fun x : Space => cvecSmulBilin (e x k) (realC (fderiv ℝ r x (ek k)))) :=
      iteratedFDeriv_sum (fun k _ => (cvecSmulBilin.isBoundedBilinearMap.contDiff.comp ((hcd_ek k).prodMk (hcd_rk' k))).of_le hm_top)
    rw [hsum, Finset.sum_apply]
    refine (norm_sum_le _ _).trans (sum3_le _ _ fun k => ?_)
    refine (cvecSmulBilin.norm_iteratedFDeriv_le_of_bilinear (hcd_ek k) (hcd_rk' k) y hm_top).trans ?_
    have hsum_le : ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun x => e x k) y‖ *
        ‖iteratedFDeriv ℝ (m - i) (fun x => realC (fderiv ℝ r x (ek k))) y‖ ≤
        2 ^ m * ((m : ℝ) + 1) * (Esum * Rsum) := by
      have hterm : ∀ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun x => e x k) y‖ *
          ‖iteratedFDeriv ℝ (m - i) (fun x => realC (fderiv ℝ r x (ek k))) y‖ ≤
          2 ^ m * (Esum * Rsum) := fun i hi => by
        have him : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        have hch : (m.choose i : ℝ) ≤ 2 ^ m := by exact_mod_cast Nat.choose_le_two_pow m i
        have he' : ‖iteratedFDeriv ℝ i (fun x => e x k) y‖ ≤ Esum := by
          have hcomp := ContinuousLinearMap.norm_iteratedFDeriv_comp_left
            ((EuclideanSpace.proj k : CVec3 →L[ℂ] ℂ).restrictScalars ℝ) he.contDiffAt
            (by simp : (i : WithTop ℕ∞) ≤ ∞) (x := y)
          refine hcomp.trans ?_
          calc ‖((EuclideanSpace.proj k : CVec3 →L[ℂ] ℂ).restrictScalars ℝ)‖ * ‖iteratedFDeriv ℝ i e y‖
              ≤ 1 * Esum := mul_le_mul (norm_projC_le_one k) (hEle i (by omega)) (norm_nonneg _) zero_le_one
            _ = Esum := one_mul _
        have hr' : ‖iteratedFDeriv ℝ (m - i) (fun x => realC (fderiv ℝ r x (ek k))) y‖ ≤ Rsum := by
          have hcomp := ContinuousLinearMap.norm_iteratedFDeriv_comp_left realCCLM
            ((ContinuousLinearMap.apply ℝ Space (ek k)).contDiff.comp (hr.fderiv_right (by simp))).contDiffAt
            (by simp : ((m - i : ℕ) : WithTop ℕ∞) ≤ ∞) (x := y)
          refine hcomp.trans ?_
          have hfd := norm_iteratedFDeriv_fderiv_apply_le hr (ek k) (m - i) y
          have hmi : m - i + 1 ≤ m + 1 := by omega
          calc ‖realCCLM‖ * ‖iteratedFDeriv ℝ (m - i) (fun x => fderiv ℝ r x (ek k)) y‖
              ≤ 1 * (‖iteratedFDeriv ℝ (m - i + 1) r y‖ * ‖ek k‖) :=
                mul_le_mul norm_realCCLM_le_one hfd (norm_nonneg _) zero_le_one
            _ ≤ 1 * (Rsum * 1) :=
                mul_le_mul_of_nonneg_left (mul_le_mul (hRle (m - i + 1) hmi) (norm_ek_le_one k)
                  (norm_nonneg _) hR0) zero_le_one
            _ = Rsum := by ring
        calc (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun x => e x k) y‖ *
              ‖iteratedFDeriv ℝ (m - i) (fun x => realC (fderiv ℝ r x (ek k))) y‖
            ≤ (2 ^ m * Esum) * Rsum :=
              mul_le_mul (mul_le_mul hch he' (norm_nonneg _) (by positivity)) hr' (norm_nonneg _) (by positivity)
          _ = 2 ^ m * (Esum * Rsum) := by ring
      calc ∑ i ∈ Finset.range (m + 1), _ ≤ ∑ _i ∈ Finset.range (m + 1), 2 ^ m * (Esum * Rsum) :=
            Finset.sum_le_sum hterm
        _ = 2 ^ m * ((m : ℝ) + 1) * (Esum * Rsum) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    calc ‖cvecSmulBilin‖ * ∑ i ∈ Finset.range (m + 1), _
        ≤ ‖cvecSmulBilin‖ * (2 ^ m * ((m : ℝ) + 1) * (Esum * Rsum)) :=
          mul_le_mul_of_nonneg_left hsum_le (norm_nonneg cvecSmulBilin)
      _ = 2 ^ m * ((m : ℝ) + 1) * ‖cvecSmulBilin‖ * Esum * Rsum := by ring
  have hsum6 := (norm6_le _ _ _ _ _ _).trans
    (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add ht1 ht2) ht3) ht4) ht5) ht6)
  have hMain : Dnorm + (1 / 2 : ℝ) * (3 * (‖smulCVecBilin‖ * 2 ^ m * ((m : ℝ) + 1) * (1 + ‖y‖) * Esum)) +
      |ν| * (3 * Esum) + (1 / 2 : ℝ) * Esum +
      3 * (2 ^ m * ((m : ℝ) + 1) * ‖smulCVecBilin‖ * Rsum * Esum) +
      3 * (2 ^ m * ((m : ℝ) + 1) * ‖cvecSmulBilin‖ * Esum * Rsum) ≤
      K * (1 + |ν|) * (1 + ‖y‖) * (1 + Rsum) * (Esum + Dnorm) := by
    have hK_def : K / 6 = max 1 (max C0 (2 ^ m * ((m : ℝ) + 1) * Bsum + 3)) := by
      dsimp [K, sfunConst, C0, Bsum]; ring
    have hK_ge_1 : 1 ≤ K / 6 := by rw [hK_def]; exact le_max_left _ _
    have hK_ge_C0 : C0 ≤ K / 6 := by rw [hK_def]; exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hK_ge_B : 2 ^ m * ((m : ℝ) + 1) * Bsum + 3 ≤ K / 6 := by
      rw [hK_def]; exact le_trans (le_max_right _ _) (le_max_right _ _)
    have h1y : 1 ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
    have h1ν : 1 ≤ 1 + |ν| := by linarith [abs_nonneg ν]
    have h1R : 1 ≤ 1 + Rsum := by linarith
    have hED : 0 ≤ Esum + Dnorm := add_nonneg hE0 hD0
    have hK0' : 0 ≤ K / 6 := le_trans zero_le_one hK_ge_1
    have hED_le : Esum ≤ Esum + Dnorm := le_add_of_nonneg_right hD0
    have ha : Dnorm ≤ (K / 6) * (1 + |ν|) * (1 + ‖y‖) * (1 + Rsum) * (Esum + Dnorm) := by
      have h0 : Dnorm ≤ (K / 6) * (Esum + Dnorm) :=
        (le_add_of_nonneg_left hE0).trans (le_mul_of_one_le_left hED hK_ge_1)
      calc Dnorm ≤ (K / 6) * (Esum + Dnorm) := h0
        _ ≤ (K / 6) * (1 + |ν|) * (Esum + Dnorm) :=
            mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hK0' h1ν) hED
        _ ≤ (K / 6) * (1 + |ν|) * (1 + ‖y‖) * (Esum + Dnorm) :=
            mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (mul_nonneg hK0' (by positivity)) h1y) hED
        _ ≤ (K / 6) * (1 + |ν|) * (1 + ‖y‖) * (1 + Rsum) * (Esum + Dnorm) :=
            mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (mul_nonneg (mul_nonneg hK0' (by positivity)) (by positivity)) h1R) hED
    have hb : (1 / 2 : ℝ) * (3 * (‖smulCVecBilin‖ * 2 ^ m * ((m : ℝ) + 1) * (1 + ‖y‖) * Esum)) ≤
        (K / 6) * (1 + |ν|) * (1 + ‖y‖) * (1 + Rsum) * (Esum + Dnorm) := by
      have h0 : (1 / 2 : ℝ) * (3 * (‖smulCVecBilin‖ * 2 ^ m * ((m : ℝ) + 1))) ≤ K / 6 := by
        have hC0 : (1 / 2 : ℝ) * (3 * (‖smulCVecBilin‖ * 2 ^ m * ((m : ℝ) + 1))) ≤ C0 := by
          dsimp [C0]
          have hnn : 0 ≤ ‖smulCVecBilin‖ * 2 ^ m * ((m : ℝ) + 1) := by positivity
          linarith
        exact hC0.trans hK_ge_C0
      have h1' : (1 / 2 : ℝ) * (3 * (‖smulCVecBilin‖ * 2 ^ m * ((m : ℝ) + 1) * (1 + ‖y‖) * Esum)) ≤
          (K / 6) * (1 + ‖y‖) * (Esum + Dnorm) := by
        calc (1 / 2 : ℝ) * (3 * (‖smulCVecBilin‖ * 2 ^ m * ((m : ℝ) + 1) * (1 + ‖y‖) * Esum))
            = ((1 / 2 : ℝ) * (3 * (‖smulCVecBilin‖ * 2 ^ m * ((m : ℝ) + 1)))) * ((1 + ‖y‖) * Esum) := by ring
          _ ≤ (K / 6) * ((1 + ‖y‖) * (Esum + Dnorm)) :=
              mul_le_mul h0 (mul_le_mul_of_nonneg_left hED_le (by positivity)) (mul_nonneg (by positivity) hE0) hK0'
          _ = (K / 6) * (1 + ‖y‖) * (Esum + Dnorm) := by ring
      calc (1 / 2 : ℝ) * (3 * (‖smulCVecBilin‖ * 2 ^ m * ((m : ℝ) + 1) * (1 + ‖y‖) * Esum))
          ≤ (K / 6) * (1 + ‖y‖) * (Esum + Dnorm) := h1'
        _ ≤ (K / 6) * (1 + |ν|) * (1 + ‖y‖) * (Esum + Dnorm) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hK0' h1ν) (by positivity)) hED
        _ ≤ (K / 6) * (1 + |ν|) * (1 + ‖y‖) * (1 + Rsum) * (Esum + Dnorm) :=
            mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (mul_nonneg (mul_nonneg hK0' (by positivity)) (by positivity)) h1R) hED
    have hc : |ν| * (3 * Esum) ≤ (K / 6) * (1 + |ν|) * (1 + ‖y‖) * (1 + Rsum) * (Esum + Dnorm) := by
      have h3K : 3 ≤ K / 6 := by
        have hnn : 0 ≤ 2 ^ m * ((m : ℝ) + 1) * Bsum := by positivity
        linarith only [hnn, hK_ge_B]
      have h1' : |ν| * (3 * Esum) ≤ (K / 6) * (1 + |ν|) * (Esum + Dnorm) := by
        calc |ν| * (3 * Esum) = 3 * |ν| * Esum := by ring
          _ ≤ (K / 6) * (1 + |ν|) * (Esum + Dnorm) :=
              mul_le_mul (mul_le_mul h3K (le_add_of_nonneg_left zero_le_one) (abs_nonneg ν) hK0')
                hED_le hE0 (mul_nonneg hK0' (by positivity))
      calc |ν| * (3 * Esum) ≤ (K / 6) * (1 + |ν|) * (Esum + Dnorm) := h1'
        _ ≤ (K / 6) * (1 + |ν|) * (1 + ‖y‖) * (Esum + Dnorm) :=
            mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (mul_nonneg hK0' (by positivity)) h1y) hED
        _ ≤ (K / 6) * (1 + |ν|) * (1 + ‖y‖) * (1 + Rsum) * (Esum + Dnorm) :=
            mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (mul_nonneg (mul_nonneg hK0' (by positivity)) (by positivity)) h1R) hED
    have hd' : (1 / 2 : ℝ) * Esum ≤ (K / 6) * (1 + |ν|) * (1 + ‖y‖) * (1 + Rsum) * (Esum + Dnorm) := by
      have h0 : (1 / 2 : ℝ) * Esum ≤ (K / 6) * (Esum + Dnorm) :=
        mul_le_mul (by linarith only [hK_ge_1]) hED_le hE0 hK0'
      calc (1 / 2 : ℝ) * Esum ≤ (K / 6) * (Esum + Dnorm) := h0
        _ ≤ (K / 6) * (1 + |ν|) * (Esum + Dnorm) :=
            mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hK0' h1ν) hED
        _ ≤ (K / 6) * (1 + |ν|) * (1 + ‖y‖) * (Esum + Dnorm) :=
            mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (mul_nonneg hK0' (by positivity)) h1y) hED
        _ ≤ (K / 6) * (1 + |ν|) * (1 + ‖y‖) * (1 + Rsum) * (Esum + Dnorm) :=
            mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (mul_nonneg (mul_nonneg hK0' (by positivity)) (by positivity)) h1R) hED
    have he' : 3 * (2 ^ m * ((m : ℝ) + 1) * ‖smulCVecBilin‖ * Rsum * Esum) ≤
        (K / 6) * (1 + |ν|) * (1 + ‖y‖) * (1 + Rsum) * (Esum + Dnorm) := by
      have hB' : 3 * (2 ^ m * ((m : ℝ) + 1) * ‖smulCVecBilin‖) ≤ K / 6 := by
        have hB1 : 3 * (2 ^ m * ((m : ℝ) + 1) * ‖smulCVecBilin‖) ≤ 2 ^ m * ((m : ℝ) + 1) * Bsum + 3 := by
          dsimp [Bsum]
          have hpow : 0 ≤ 2 ^ m * ((m : ℝ) + 1) := by positivity
          have hc_nn : 0 ≤ 2 ^ m * ((m : ℝ) + 1) * ‖cvecSmulBilin‖ := mul_nonneg hpow (norm_nonneg cvecSmulBilin)
          linarith only [hc_nn]
        exact hB1.trans hK_ge_B
      have h1' : 3 * (2 ^ m * ((m : ℝ) + 1) * ‖smulCVecBilin‖ * Rsum * Esum) ≤
          (K / 6) * (1 + Rsum) * (Esum + Dnorm) := by
        calc 3 * (2 ^ m * ((m : ℝ) + 1) * ‖smulCVecBilin‖ * Rsum * Esum)
            = (3 * (2 ^ m * ((m : ℝ) + 1) * ‖smulCVecBilin‖)) * Rsum * Esum := by ring
          _ ≤ (K / 6) * (1 + Rsum) * (Esum + Dnorm) :=
              mul_le_mul (mul_le_mul hB' (le_add_of_nonneg_left zero_le_one) hR0 hK0')
                hED_le hE0 (mul_nonneg hK0' (by positivity))
      calc 3 * (2 ^ m * ((m : ℝ) + 1) * ‖smulCVecBilin‖ * Rsum * Esum)
          ≤ (K / 6) * (1 + Rsum) * (Esum + Dnorm) := h1'
        _ ≤ (K / 6) * (1 + |ν|) * (1 + Rsum) * (Esum + Dnorm) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hK0' h1ν) (by positivity)) hED
        _ ≤ (K / 6) * (1 + |ν|) * (1 + ‖y‖) * (1 + Rsum) * (Esum + Dnorm) := by
            have h11 : (K / 6) * (1 + |ν|) * (1 + Rsum) ≤ (K / 6) * (1 + |ν|) * (1 + ‖y‖) * (1 + Rsum) :=
              mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (mul_nonneg hK0' (by positivity)) h1y) (by positivity)
            exact mul_le_mul_of_nonneg_right h11 hED
    have hf' : 3 * (2 ^ m * ((m : ℝ) + 1) * ‖cvecSmulBilin‖ * Esum * Rsum) ≤
        (K / 6) * (1 + |ν|) * (1 + ‖y‖) * (1 + Rsum) * (Esum + Dnorm) := by
      have hB' : 3 * (2 ^ m * ((m : ℝ) + 1) * ‖cvecSmulBilin‖) ≤ K / 6 := by
        have hB1 : 3 * (2 ^ m * ((m : ℝ) + 1) * ‖cvecSmulBilin‖) ≤ 2 ^ m * ((m : ℝ) + 1) * Bsum + 3 := by
          dsimp [Bsum]
          have hpow : 0 ≤ 2 ^ m * ((m : ℝ) + 1) := by positivity
          have hs_nn : 0 ≤ 2 ^ m * ((m : ℝ) + 1) * ‖smulCVecBilin‖ := mul_nonneg hpow (norm_nonneg smulCVecBilin)
          linarith only [hs_nn]
        exact hB1.trans hK_ge_B
      have h1' : 3 * (2 ^ m * ((m : ℝ) + 1) * ‖cvecSmulBilin‖ * Esum * Rsum) ≤
          (K / 6) * (1 + Rsum) * (Esum + Dnorm) := by
        calc 3 * (2 ^ m * ((m : ℝ) + 1) * ‖cvecSmulBilin‖ * Esum * Rsum)
            = (3 * (2 ^ m * ((m : ℝ) + 1) * ‖cvecSmulBilin‖)) * Rsum * Esum := by ring
          _ ≤ (K / 6) * (1 + Rsum) * (Esum + Dnorm) :=
              mul_le_mul (mul_le_mul hB' (le_add_of_nonneg_left zero_le_one) hR0 hK0')
                hED_le hE0 (mul_nonneg hK0' (by positivity))
      calc 3 * (2 ^ m * ((m : ℝ) + 1) * ‖cvecSmulBilin‖ * Esum * Rsum)
          ≤ (K / 6) * (1 + Rsum) * (Esum + Dnorm) := h1'
        _ ≤ (K / 6) * (1 + |ν|) * (1 + Rsum) * (Esum + Dnorm) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hK0' h1ν) (by positivity)) hED
        _ ≤ (K / 6) * (1 + |ν|) * (1 + ‖y‖) * (1 + Rsum) * (Esum + Dnorm) := by
            have h11 : (K / 6) * (1 + |ν|) * (1 + Rsum) ≤ (K / 6) * (1 + |ν|) * (1 + ‖y‖) * (1 + Rsum) :=
              mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (mul_nonneg hK0' (by positivity)) h1y) (by positivity)
            exact mul_le_mul_of_nonneg_right h11 hED
    linarith only [ha, hb, hc, hd', he', hf']
  exact hsum6.trans hMain

end SfunAll

private lemma inletNearAll_calc (ν : ℝ) (e s : ℝ × Space → EuclideanSpace ℂ (Fin 3)) (r : ℝ → Space → Space)
    (m : ℕ) (β : Fin m → Fin 3)
    (R0 : ℝ) (hR0 : 0 < R0) (hR : ContDiff ℝ ∞ (fun x : ℝ × Space => r x.1 x.2))
    (hE : ContDiff ℝ ∞ e) (hSrc : ContDiff ℝ ∞ s)
    (hSlice : ∀ τ z, s (τ, z) =
      Jets.Sfun (fun z => e (τ, z)) (fun z => UnforcedLeray.PhaseSpace.dτ e (τ, z)) (r τ) ν z)
    (CE : ℝ)
    (hCE : ∀ τ (y : Space), Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ≤ R0 →
      (∀ k ≤ m + 2, ‖iteratedFDeriv ℝ k (fun z : Space => e (τ, z)) y‖ ≤
        CE * (1 + |y 2|) ^ (-3 : ℝ)) ∧
      (∀ k ≤ m, ‖iteratedFDeriv ℝ k (fun z : Space => UnforcedLeray.PhaseSpace.dτ e (τ, z)) y‖ ≤
        CE * (1 + |y 2|) ^ (-3 : ℝ)))
    (RsumBound : ℝ) (hRsum0 : 0 ≤ RsumBound)
    (hR_bd_all : ∀ (τ : ℝ) (y : Space),
      ∑ k ∈ Finset.range (m + 2), ‖iteratedFDeriv ℝ k (r τ) y‖ ≤ RsumBound) :
    ∃ C : ℝ, ∀ τ : ℝ, ∀ y : Space, Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ≤ R0 →
      ‖iterDyRev β s (τ, y)‖ ≤ C * (1 + |y 2|) ^ (-2 : ℝ) := by
  have hK0 : 0 ≤ sfunConst m := sfunConst_nonneg m
  obtain ⟨C, hC_eq⟩ : ∃ x : ℝ,
      x = sfunConst m * (1 + |ν|) * (1 + R0) * (1 + RsumBound) * (((m : ℝ) + 4) * max CE 0) :=
    ⟨_, rfl⟩
  refine ⟨C, fun τ y hy => ?_⟩
  have hslice := RawIterEnvSub.norm_iterDyRev_le_slice isOpen_univ hSrc.contDiffOn β (mem_univ (τ, y))
  have he_cd : ContDiff ℝ ∞ (fun z => e (τ, z)) :=
    hE.comp (contDiff_const.prodMk contDiff_id)
  have hd_cd : ContDiff ℝ ∞ (fun z => UnforcedLeray.PhaseSpace.dτ e (τ, z)) :=
    (UnforcedLeray.PhaseSpace.contDiff_dτ hE).comp (contDiff_const.prodMk contDiff_id)
  have hr_cd : ContDiff ℝ ∞ (r τ) :=
    hR.comp (contDiff_const.prodMk contDiff_id)
  have hEq : (fun z : Space => s (τ, z)) =
      Jets.Sfun (fun z => e (τ, z))
        (fun z => UnforcedLeray.PhaseSpace.dτ e (τ, z)) (r τ) ν :=
    funext fun z => hSlice τ z
  have hSf := norm_iteratedFDeriv_Sfun_le (fun z => e (τ, z))
    (fun z => UnforcedLeray.PhaseSpace.dτ e (τ, z)) (r τ) ν
    he_cd hd_cd hr_cd m y
  obtain ⟨hE_bd, hD_bd⟩ := hCE τ y hy
  have hR_bd : ∑ k ∈ Finset.range (m + 2), ‖iteratedFDeriv ℝ k (r τ) y‖ ≤ RsumBound :=
    hR_bd_all τ y
  have hED_bd : (∑ k ∈ Finset.range (m + 3),
      ‖iteratedFDeriv ℝ k (fun z : Space => e (τ, z)) y‖) +
      ‖iteratedFDeriv ℝ m (fun z : Space => UnforcedLeray.PhaseSpace.dτ e (τ, z)) y‖ ≤
      ((m : ℝ) + 4) * max CE 0 * (1 + |y 2|) ^ (-3 : ℝ) := by
    have hp3 : 0 ≤ (1 + |y 2|) ^ (-3 : ℝ) := by positivity
    have hE' : ∑ k ∈ Finset.range (m + 3),
        ‖iteratedFDeriv ℝ k (fun z : Space => e (τ, z)) y‖ ≤
        ((m : ℝ) + 3) * (max CE 0 * (1 + |y 2|) ^ (-3 : ℝ)) := by
      calc ∑ k ∈ Finset.range (m + 3), _
          ≤ ∑ _k ∈ Finset.range (m + 3), max CE 0 * (1 + |y 2|) ^ (-3 : ℝ) := by
              refine Finset.sum_le_sum fun k hk => ?_
              have hk' : k ≤ m + 2 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
              exact (hE_bd k hk').trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp3)
        _ = ((m : ℝ) + 3) * (max CE 0 * (1 + |y 2|) ^ (-3 : ℝ)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    have hD' : ‖iteratedFDeriv ℝ m (fun z : Space => UnforcedLeray.PhaseSpace.dτ e (τ, z)) y‖ ≤
        max CE 0 * (1 + |y 2|) ^ (-3 : ℝ) :=
      (hD_bd m (by omega)).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp3)
    calc _ ≤ ((m : ℝ) + 3) * (max CE 0 * (1 + |y 2|) ^ (-3 : ℝ)) +
          max CE 0 * (1 + |y 2|) ^ (-3 : ℝ) := add_le_add hE' hD'
      _ = ((m : ℝ) + 4) * max CE 0 * (1 + |y 2|) ^ (-3 : ℝ) := by ring
  have hy_norm : 1 + ‖y‖ ≤ (1 + R0) * (1 + |y 2|) := by
    have hny : ‖y‖ ≤ R0 + |y 2| := by
      have hsq : ‖y‖ ^ 2 = (Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) ^ 2 + |y 2| ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
        rw [Real.sq_sqrt (by positivity)]
      have hle : ‖y‖ ^ 2 ≤ (R0 + |y 2|) ^ 2 := by
        have hsq_le : (Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) ^ 2 ≤ R0 ^ 2 :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) hy 2
        nlinarith only [hsq, hsq_le, abs_nonneg (y 2), hR0]
      nlinarith only [hle, norm_nonneg y, abs_nonneg (y 2), hR0]
    nlinarith only [hny, abs_nonneg (y 2), hR0]
  have hpow : (1 + |y 2|) * (1 + |y 2|) ^ (-3 : ℝ) = (1 + |y 2|) ^ (-2 : ℝ) := by
    have hp : 0 < 1 + |y 2| := by positivity
    calc (1 + |y 2|) * (1 + |y 2|) ^ (-3 : ℝ)
        = (1 + |y 2|) ^ (1 : ℝ) * (1 + |y 2|) ^ (-3 : ℝ) := by rw [Real.rpow_one]
      _ = (1 + |y 2|) ^ ((1 : ℝ) + (-3 : ℝ)) := (Real.rpow_add hp 1 (-3)).symm
      _ = (1 + |y 2|) ^ (-2 : ℝ) := by norm_num
  calc ‖iterDyRev β s (τ, y)‖
      ≤ ‖iteratedFDeriv ℝ m (fun z : Space => s (τ, z)) y‖ := hslice
    _ = ‖iteratedFDeriv ℝ m (Jets.Sfun (fun z => e (τ, z))
          (fun z => UnforcedLeray.PhaseSpace.dτ e (τ, z)) (r τ) ν) y‖ := by
        rw [hEq]
    _ ≤ sfunConst m * (1 + |ν|) * (1 + ‖y‖) *
          (1 + ∑ k ∈ Finset.range (m + 2), ‖iteratedFDeriv ℝ k (r τ) y‖) *
          ((∑ k ∈ Finset.range (m + 3), ‖iteratedFDeriv ℝ k (fun z => e (τ, z)) y‖) +
            ‖iteratedFDeriv ℝ m (fun z => UnforcedLeray.PhaseSpace.dτ e (τ, z)) y‖) := hSf
    _ ≤ sfunConst m * (1 + |ν|) * ((1 + R0) * (1 + |y 2|)) * (1 + RsumBound) *
          (((m : ℝ) + 4) * max CE 0 * (1 + |y 2|) ^ (-3 : ℝ)) := by
        have h_pre0 : 0 ≤ sfunConst m * (1 + |ν|) := mul_nonneg hK0 (by positivity)
        have h_pre1 : 0 ≤ sfunConst m * (1 + |ν|) * ((1 + R0) * (1 + |y 2|)) :=
          mul_nonneg h_pre0 (mul_nonneg (by positivity) (by positivity))
        have h_pre2 : 0 ≤ sfunConst m * (1 + |ν|) * ((1 + R0) * (1 + |y 2|)) * (1 + RsumBound) :=
          mul_nonneg h_pre1 (add_nonneg zero_le_one hRsum0)
        have h_ed0 : 0 ≤ (∑ k ∈ Finset.range (m + 3),
            ‖iteratedFDeriv ℝ k (fun z : Space => e (τ, z)) y‖) +
            ‖iteratedFDeriv ℝ m (fun z : Space => UnforcedLeray.PhaseSpace.dτ e (τ, z)) y‖ :=
          add_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) (norm_nonneg _)
        refine mul_le_mul ?_ hED_bd h_ed0 h_pre2
        refine mul_le_mul ?_ (add_le_add_right hR_bd 1)
          (add_nonneg zero_le_one (Finset.sum_nonneg fun _ _ => norm_nonneg _)) h_pre1
        exact mul_le_mul_of_nonneg_left hy_norm h_pre0
    _ = C * ((1 + |y 2|) * (1 + |y 2|) ^ (-3 : ℝ)) := by rw [hC_eq]; ring
    _ = C * (1 + |y 2|) ^ (-2 : ℝ) := by rw [hpow]

/-- **All-order near-axis bound on `iterDyRev β (inletSrc p i)`**:
with a single viscosity threshold `ν₀ > 0` independent of `m`, for any `R0 > 0` and any `m`, `β`,
`‖iterDyRev β (inletSrc p i) (τ, y)‖ ≤ C * (1 + |y 2|) ^ (-2 : ℝ)` on `ϱ y ≤ R0`. -/
theorem inletNearAll (lam : ℂ) (q : Planar.Profile) (hq : Planar.IsGrowingEigenpair lam q)
    (dm dp : ℝ) (hdm : 0 < dm) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.mode = q →
      ∀ (i : Fin 2) (m : ℕ) (β : Fin m → Fin 3) (R0 : ℝ), 0 < R0 → ∃ C : ℝ,
        ∀ τ ∈ Ioc (0 : ℝ) p.period, ∀ y : Space,
          Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ≤ R0 →
            ‖iterDyRev β (inletSrc p i) (τ, y)‖ ≤ C * (1 + |y 2|) ^ (-2 : ℝ) := by
  obtain ⟨ν1, hν1, H1⟩ := rawAllDerivsBdd_proof dm dp hdm
  obtain ⟨ν2, hν2, H2⟩ := rawJointSmooth dm dp hdm
  refine ⟨min (min ν1 ν2) 1, lt_min (lt_min hν1 hν2) one_pos,
    fun p d hreg hν hm i m β R0 hR0 => ?_⟩
  have h1 : p.ν ≤ ν1 := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have h2 : p.ν ≤ ν2 := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have h3 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  have hR := H2 p d hreg h2
  have hI := inlet_contDiff_joint lam q hq hreg h3 hm i
  have hE : ContDiff ℝ ∞ (p.Efun i) := contDiff_realC_meas.comp hI
  have hSrc : ContDiff ℝ ∞ (inletSrc p i) := inletSrc_contDiff hE hR
  obtain ⟨CE, hCE⟩ := inletENearJetsAll lam q hq dm dp hdm p d hreg h3 hm i (m + 2) 3 R0 hR0
  have hRall : ∀ k : ℕ, ∃ C : ℝ, ∀ (τ : ℝ) (y : Space),
      ‖iteratedFDeriv ℝ k (p.raw τ) y‖ ≤ C :=
    fun k => H1 p d hreg h1 k
  choose Cr hCr using hRall
  obtain ⟨RsumBound, hRsum_eq⟩ : ∃ x : ℝ, x = ∑ k ∈ Finset.range (m + 2), max (Cr k) 0 := ⟨_, rfl⟩
  have hRsum0 : 0 ≤ RsumBound := by
    rw [hRsum_eq]; exact Finset.sum_nonneg fun _ _ => le_max_right _ _
  have hR_bd_all : ∀ (τ : ℝ) (y : Space),
      ∑ k ∈ Finset.range (m + 2), ‖iteratedFDeriv ℝ k (p.raw τ) y‖ ≤ RsumBound := fun τ y => by
    rw [hRsum_eq]
    exact Finset.sum_le_sum fun k _ => (hCr k τ y).trans (le_max_left _ _)
  have hCE' : ∀ τ (y : Space), Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ≤ R0 →
      (∀ k ≤ m + 2, ‖iteratedFDeriv ℝ k (fun z : Space => p.Efun i (τ, z)) y‖ ≤
        CE * (1 + |y 2|) ^ (-3 : ℝ)) ∧
      (∀ k ≤ m, ‖iteratedFDeriv ℝ k (fun z : Space => UnforcedLeray.PhaseSpace.dτ (p.Efun i) (τ, z)) y‖ ≤
        CE * (1 + |y 2|) ^ (-3 : ℝ)) := fun τ y hy =>
    ⟨fun k hk => by
       have h1 := (hCE τ y hy).1 k hk
       rwa [show (-(3 : ℕ) : ℝ) = (-3 : ℝ) by norm_num] at h1,
     fun k hk => by
       have h2 := (hCE τ y hy).2 k (by omega)
       rwa [show (-(3 : ℕ) : ℝ) = (-3 : ℝ) by norm_num] at h2⟩
  obtain ⟨C, hC⟩ := inletNearAll_calc p.ν (p.Efun i) (inletSrc p i) p.raw m β R0 hR0
    hR hE hSrc (fun τ z => inletSrc_slice p i hE τ z) CE hCE' RsumBound hRsum0 hR_bd_all
  exact ⟨C, fun τ _hτ y hy => hC τ y hy⟩

end UnforcedLeray.Short.IIb.IterInletSub
