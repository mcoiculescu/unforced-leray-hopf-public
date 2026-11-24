import UnforcedLeray.Short.PartI.Sub.PartI_T08_2
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.HasDeriv
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.CellToolkit

/-!
# Part I, task `PartI:T08/2/2` (`TrainVelocityJetL2`): decomposition

Source of record: `the November 2 reference manuscript`, lines 261-288:

> The datum is divergence free and belongs to `BUC ∩ H^k` for every `k` ... It is also the
> finite-energy solution ... Approximation and transverse cutoffs then give the velocity and
> vorticity energy identities. The scalar vorticity equation preserves zero circulation ...

The target `TrainVelocityJetL2` (`Sub/PartI_T08_2.lean`): for a BUC train, at every age `s > 0`
every word derivative `∂_w v_k(s)` is in `L²` of one cell.

## Route (the vorticity energy with transverse cutoffs, then `Δv = ∇^⊥ω`)

`IsBUCTrain` bounds every spatial derivative of `v` on `[0, S] × ℝ²` but gives no `L²`
information; the `L²` information is propagated from the datum (`H^∞`) by a transverse-cutoff
energy argument.  It is run on the vorticity `ω = curl v` (lines 286-287), whose equation
`ω_s + v·∇ω = νΔω` has no pressure (the velocity jets would need bounds on `∂_w p`, which neither
`B0140.IsTrain` nor `IsBUCTrain` provides).

1. **Vorticity jets.**  `F_R^j(s) = ∫_cell χ_R(η) Σ_{|u| ≤ j} (∂_u ω(s))²` (`vortJetEnergy`,
   `χ_R = etaCutoff R`) is continuous on `[0, S]` and `F_R' ≤ C F_R + C` on `(0, S)` with `C`
   independent of `R ≥ 1` (`VortJetEnergyIneq`; the cutoff errors are `O(1)` by the uniform bounds
   of `IsBUCTrain` on the strip `R ≤ |η| ≤ 2R` of area `2Rc`, and the commutator
   `[∂_u, v·∇]ω` is bounded by the jet itself).  Gronwall (`CutoffGronwall`, proved here) and the
   datum (`TrainDatumWordL2`, `v(0) = trainDatum c`) give `F_R^j(s) ≤ B` for all `R ≥ 1`, and
   monotone convergence (`CutoffL2OfBound`) gives `∂_u ω(s) ∈ L²(cell)`.
2. **Velocity jets** (static, by induction on the word).  `w = []` is `finite_energy`.  For
   `h = ∂_{w'} v_k`, `Δh = ∓∂_{β} ∂_{w'} ω` (`TrainVelocityWordLap`, from `div v = 0`), so
   `h, Δh ∈ L²` and the bounded `h, ∇h` give `∇h ∈ L²` (`GradL2OfLapL2`: cutoff integration by
   parts `∫ χ_R |∇h|² = -∫ χ_R h Δh - ∫ χ_R' h ∂_η h`).

`trainVelocityJetL2_of` derives `TrainVelocityJetL2` from the leaves `TrainDatumWordL2`,
`VortJetEnergyIneq`, `CutoffGronwall`, `CutoffL2OfBound`, `GradL2OfLapL2`,
`TrainVelocityWordLap`.  Proved here: `cutoffGronwall_proof`, the uniform word bound
`vjl_wordBoundedOn` (from `IsBUCTrain`), and `vortWord_eq` (`∂_u ω` as a difference of velocity
words).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-! ### Vocabulary -/

/-- The words of length at most `j` (`true` is `∂_q`, `false` is `∂_η`). -/
def wordsUpTo (j : ℕ) : Finset (List Bool) := (Finset.range (j + 1)).biUnion wordsOfLength

/-- The word derivative `∂_u ω(s)` of the vorticity `ω = curl v = ∂_q v_η - ∂_η v_q` of the
train at age `s` (line 286: the scalar vorticity). -/
def vortWord {ν c : ℝ} (tr : B0140.TrainSol ν c) (u : List Bool) (s : ℝ) : Plane → ℝ :=
  B0151.derivWord u (Cyl.curl (tr.v s))

/-- The transverse-cutoff vorticity jet energy
`F_R^j(s) = ∫_cell χ_R(η) Σ_{|u| ≤ j} (∂_u ω(s))²` (lines 286-287, "transverse cutoffs ...
vorticity energy identities"). -/
def vortJetEnergy {ν c : ℝ} (tr : B0140.TrainSol ν c) (j : ℕ) (R s : ℝ) : ℝ :=
  ∫ z in Cyl.cell c, etaCutoff R z.2 * ∑ u ∈ wordsUpTo j, vortWord tr u s z ^ 2

theorem vjl_mem_wordsOfLength {l : ℕ} {u : List Bool} :
    u ∈ wordsOfLength l ↔ u.length = l := by
  unfold wordsOfLength
  constructor
  · intro h
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 h
    exact List.length_ofFn
  · intro h
    subst h
    exact Finset.mem_image.2 ⟨u.get, Finset.mem_univ _, List.ofFn_get u⟩

theorem mem_wordsUpTo {j : ℕ} {u : List Bool} : u ∈ wordsUpTo j ↔ u.length ≤ j := by
  unfold wordsUpTo
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨l, hl, hu⟩
    rw [vjl_mem_wordsOfLength.1 hu]
    exact Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
  · intro h
    exact ⟨u.length, Finset.mem_range.2 (Nat.lt_succ_of_le h), vjl_mem_wordsOfLength.2 rfl⟩

/-! ### The leaves -/

/-- **Leaf (the datum is in `H^∞`)** (lines 262-268: the datum `v(0) = ∑ₙ ∇^⊥(-2e^{-|x-nc|²/4})`
"belongs to `BUC ∩ H^k` for every `k`").  Every word derivative of every component of
`B0140.trainDatum c` is in `L²` of one cell.  Route: `B0238.integrableOn_weight_jet_trainDatum`
with `m = 0`, `p = 2` (`∫_cell ‖D^j trainDatum‖² < ∞`), and the pointwise bound
`|∂_w f_k| ≤ ‖D^{|w|} f‖` (`cylJetWord_proof`, `‖EuclideanSpace.proj k‖ ≤ 1`, as in
`Tasks/DifferentiatedEnergy/ErrBasic/WordBounded.lean`). -/
def TrainDatumWordL2 : Prop :=
  ∀ c : ℝ, 0 < c → ∀ (w : List Bool) (k : Fin 2),
    MemLp (wordComp w (B0140.trainDatum c) k) 2 (Cyl.cellμ c)

/-- **Leaf (the cutoff vorticity jet energy inequality)** (lines 276-288: the train is the `BUC`
solution, "transverse cutoffs then give the velocity and vorticity energy identities", the scalar
vorticity equation).  For a BUC train, a jet order `j` and a horizon `S > 0` there is `C ≥ 0` such
that for every `R ≥ 1` the cutoff vorticity jet energy `F_R = vortJetEnergy tr j R` is continuous
on `[0, S]` and, at every `s ∈ (0, S)`, differentiable with `F_R'(s) ≤ C F_R(s) + C`.
(Derivation: `∂_s ∂_u ω = νΔ∂_u ω - ∂_u(v·∇ω)`; `2ν ∫ χ_R ∂_uω Δ∂_uω ≤ -2ν∫ χ_R' ∂_uω ∂_η∂_uω`;
`-2∫ χ_R ∂_uω (v·∇)∂_uω = ∫ χ_R' v_η (∂_uω)²` since `div v = 0`; both are `O(1)` by the
`IsBUCTrain` bounds on the strip `R ≤ |η| ≤ 2R ∩ cell` of area `2Rc` and `|χ_R'| ≤ C₀/R`; the
commutator `|∂_u(v·∇ω) - v·∇∂_uω| ≤ K Σ_{|u'| ≤ |u|} |∂_{u'}ω|` by Leibniz with bounded words of
`v`, giving `K' F_R`.)  Decomposed further in `Sub/PartI_T08_2_2/EnergyIneq.lean`. -/
def VortJetEnergyIneq : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr →
    ∀ (j : ℕ) (S : ℝ), 0 < S → ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
      ContinuousOn (vortJetEnergy tr j R) (Icc 0 S) ∧
      ∀ s ∈ Ioo (0 : ℝ) S, ∃ D : ℝ, HasDerivAt (vortJetEnergy tr j R) D s ∧
        D ≤ C * vortJetEnergy tr j R s + C

/-- **Leaf (Gronwall with an interior derivative)** (real analysis).  If `F` is continuous on
`[0, S]` and `F' ≤ C F + C` on `(0, S)`, then `F(s) ≤ (F(0) + 1) e^{Cs}` on `[0, S]`
(`(F + 1) e^{-Ct}` is antitone).  Proved below (`cutoffGronwall_proof`). -/
def CutoffGronwall : Prop :=
  ∀ (F : ℝ → ℝ) (S C : ℝ), 0 < S → 0 ≤ C → ContinuousOn F (Icc 0 S) →
    (∀ s ∈ Ioo (0 : ℝ) S, ∃ D : ℝ, HasDerivAt F D s ∧ D ≤ C * F s + C) →
    ∀ s ∈ Icc (0 : ℝ) S, F s ≤ (F 0 + 1) * Real.exp (C * s)

/-- **Leaf (`R → ∞`, monotone convergence)**.  A continuous `f` whose transverse-cutoff energies
`∫_cell χ_R f²` are bounded by `B` for all `R ≥ 1` is in `L²` of the cell.  Route:
`χ_n → 1` pointwise and increasing in `n` (`etaCutoff`, `Real.smoothTransition` monotone;
`χ_R = 1` for `|η| ≤ R`), so `∫⁻_cell f² ≤ liminf ∫⁻ χ_n f² ≤ B` (Fatou,
`lintegral_liminf_le`, or `lintegral_iSup`); `memLp_two_iff_integrable_sq`. -/
def CutoffL2OfBound : Prop :=
  ∀ (c B : ℝ) (f : Plane → ℝ), 0 < c → Continuous f →
    (∀ R : ℝ, 1 ≤ R → ∫ z in Cyl.cell c, etaCutoff R z.2 * f z ^ 2 ≤ B) →
    MemLp f 2 (Cyl.cellμ c)

/-- **Leaf (gradient from the Laplacian, cutoff integration by parts)** (lines 286-287,
"transverse cutoffs").  A smooth `c`-periodic `h` with `h`, `∂_q h`, `∂_η h` bounded and
`h, Δh ∈ L²(cell)` has `∂_q h, ∂_η h ∈ L²(cell)`.  Route: by `CellDerivZero` (cell IBP of
`G = χ_R h ∂_q h` and `G = χ_R h ∂_η h`, which vanish for `|η| ≥ 2R`),
`∫ χ_R (|∂_q h|² + |∂_η h|²) = -∫ χ_R h Δh - ∫ χ_R' h ∂_η h ≤ ‖h‖₂ ‖Δh‖₂ + (C₀/R) M² · 2Rc`
(`EtaCutoffFacts`: `|χ_R'| ≤ C₀/R`, supported in `R ≤ |η| ≤ 2R`); then `CutoffL2OfBound`'s
argument (monotone convergence) for `∂_q h` and `∂_η h`. -/
def GradL2OfLapL2 : Prop :=
  ∀ (c : ℝ) (h : Plane → ℝ), 0 < c → ContDiff ℝ ∞ h → Cyl.IsPeriodic c h →
    (∃ M : ℝ, ∀ z : Plane, |h z| ≤ M ∧ |Cyl.partialQ h z| ≤ M ∧ |Cyl.partialEta h z| ≤ M) →
    MemLp h 2 (Cyl.cellμ c) → MemLp (Train.lapS h) 2 (Cyl.cellμ c) →
    MemLp (Cyl.partialQ h) 2 (Cyl.cellμ c) ∧ MemLp (Cyl.partialEta h) 2 (Cyl.cellμ c)

/-- **Leaf (`Δv = ∇^⊥ω` on word derivatives)** (line 261, `v = ∇^⊥ψ`; `div v = 0`).  For a train
at age `s ≥ 0` and every word `w`: `Δ ∂_w v_q = -∂_η ∂_w ω` and `Δ ∂_w v_η = ∂_q ∂_w ω`.
Route: `v(s)` is smooth (`TrainErrorEquation.contDiff_slice`) and divergence free
(`solenoidal`); `Δv_q = ∂_q(∂_q v_q + ∂_η v_η) - ∂_η(∂_q v_η - ∂_η v_q)`,
`Δv_η = ∂_η(∂_q v_q + ∂_η v_η) + ∂_q(∂_q v_η - ∂_η v_q)`; word derivatives of smooth functions
commute (symmetry of `iteratedFDeriv`, `B0151.partialX_eq_fderiv`, `derivWord_sub_smooth`). -/
def TrainVelocityWordLap : Prop :=
  ∀ ν c : ℝ, 0 < c → ∀ tr : B0140.TrainSol ν c, ∀ s : ℝ, 0 ≤ s →
    ∀ (w : List Bool) (z : Plane),
      Train.lapS (wordComp w (tr.v s) 0) z = -vortWord tr (false :: w) s z ∧
      Train.lapS (wordComp w (tr.v s) 1) z = vortWord tr (true :: w) s z

/-! ### Proved here: Gronwall -/

/-- **`CutoffGronwall`** (proved). -/
theorem cutoffGronwall_proof : CutoffGronwall := by
  intro F S C hS _hC hcont hder s hs
  have hEc : Continuous (fun t : ℝ => Real.exp (-(C * t))) :=
    Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)
  have hGc : ContinuousOn (fun t => (F t + 1) * Real.exp (-(C * t))) (Icc 0 S) :=
    (hcont.add continuousOn_const).mul hEc.continuousOn
  have hGd : ∀ t ∈ Ioo (0 : ℝ) S, ∃ D : ℝ,
      HasDerivAt (fun t => (F t + 1) * Real.exp (-(C * t))) D t ∧ D ≤ 0 := by
    intro t ht
    obtain ⟨D, hD, hDle⟩ := hder t ht
    have he : HasDerivAt (fun t : ℝ => Real.exp (-(C * t))) (Real.exp (-(C * t)) * -(C * 1)) t :=
      ((hasDerivAt_id' t).const_mul C).neg.exp
    refine ⟨D * Real.exp (-(C * t)) + (F t + 1) * (Real.exp (-(C * t)) * -(C * 1)),
      (hD.add_const 1).mul he, ?_⟩
    have hpos := Real.exp_pos (-(C * t))
    have e : D * Real.exp (-(C * t)) + (F t + 1) * (Real.exp (-(C * t)) * -(C * 1)) =
        (D - (C * F t + C)) * Real.exp (-(C * t)) := by ring
    rw [e]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le
  have hanti : AntitoneOn (fun t => (F t + 1) * Real.exp (-(C * t))) (Icc 0 S) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 S) hGc
    · rw [interior_Icc]
      intro t ht
      obtain ⟨D, hD, _⟩ := hGd t ht
      exact hD.differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      obtain ⟨D, hD, hle⟩ := hGd t ht
      rw [hD.deriv]
      exact hle
  have h0 : (0 : ℝ) ∈ Icc 0 S := ⟨le_rfl, hS.le⟩
  have hGs := hanti h0 hs hs.1
  simp only [mul_zero, neg_zero, Real.exp_zero, mul_one] at hGs
  have hpos : 0 < Real.exp (C * s) := Real.exp_pos _
  have e : Real.exp (-(C * s)) * Real.exp (C * s) = 1 := by
    rw [← Real.exp_add]
    simp
  have hmain : F s + 1 ≤ (F 0 + 1) * Real.exp (C * s) :=
    calc F s + 1 = (F s + 1) * Real.exp (-(C * s)) * Real.exp (C * s) := by
          rw [mul_assoc, e, mul_one]
      _ ≤ (F 0 + 1) * Real.exp (C * s) := mul_le_mul_of_nonneg_right hGs hpos.le
  linarith

/-! ### Proved here: calculus of the train words -/

theorem vjl_derivWord_append (b : Bool) (h : Plane → ℝ) :
    ∀ u : List Bool, B0151.derivWord (u ++ [b]) h = B0151.derivWord u (B0151.derivWord [b] h)
  | [] => rfl
  | true :: u => by
      show GaussianVortex.partialX (B0151.derivWord (u ++ [b]) h) = _
      rw [vjl_derivWord_append b h u]
      rfl
  | false :: u => by
      show GaussianVortex.partialY (B0151.derivWord (u ++ [b]) h) = _
      rw [vjl_derivWord_append b h u]
      rfl

theorem vjl_slice_smooth {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s) (k : Fin 2) :
    ContDiff ℝ ∞ (fun x => tr.v s x k) :=
  (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp
    (TrainErrorEquation.contDiff_slice tr.isTrain.smooth_v hs)

/-- `∂_u ω = ∂_u ∂_q v_η - ∂_u ∂_η v_q`, as velocity words (`u ++ [β]`: `∂_β` first). -/
theorem vortWord_eq {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s) (u : List Bool)
    (z : Plane) :
    vortWord tr u s z =
      wordComp (u ++ [true]) (tr.v s) 1 z - wordComp (u ++ [false]) (tr.v s) 0 z := by
  have h1 := B0151.contDiff_derivWord (vjl_slice_smooth tr hs 1) [true]
  have h0 := B0151.contDiff_derivWord (vjl_slice_smooth tr hs 0) [false]
  have e : Cyl.curl (tr.v s) = fun x => B0151.derivWord [true] (fun y => tr.v s y 1) x -
      B0151.derivWord [false] (fun y => tr.v s y 0) x := rfl
  unfold vortWord wordComp
  rw [e, derivWord_sub_smooth h1 h0 u z, vjl_derivWord_append, vjl_derivWord_append]

theorem vjl_vortWord_contDiff {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (u : List Bool) : ContDiff ℝ ∞ (vortWord tr u s) := by
  have e : vortWord tr u s = fun z => wordComp (u ++ [true]) (tr.v s) 1 z -
      wordComp (u ++ [false]) (tr.v s) 0 z := funext (vortWord_eq tr hs u)
  rw [e]
  exact (B0151.contDiff_derivWord (vjl_slice_smooth tr hs 1) _).sub
    (B0151.contDiff_derivWord (vjl_slice_smooth tr hs 0) _)

/-- **Uniform word bounds on `[0, S]`** (lines 270-288, `BUC`): `IsBUCTrain.deriv_bound` and
`|∂_w f_k| ≤ ‖D^{|w|} f‖` (the proof of `trainWordBounded_proof`, uniform in `s ∈ [0, S]`). -/
theorem vjl_wordBoundedOn {ν c : ℝ} {tr : B0140.TrainSol ν c} (htr : IsBUCTrain tr) {S : ℝ}
    (hS : 0 ≤ S) (w : List Bool) (k : Fin 2) :
    ∃ M : ℝ, ∀ s ∈ Icc (0 : ℝ) S, ∀ z : Plane, |wordComp w (tr.v s) k z| ≤ M := by
  obtain ⟨M0, hM0⟩ := IsBUCTrain.deriv_bound htr hS w.length
  have hproj : ‖(EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
      simpa using PiLp.norm_apply_le x k)
  have hj : ((w.length : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  refine ⟨M0, fun s hs z => ?_⟩
  have hv : ContDiff ℝ ∞ (tr.v s) := TrainErrorEquation.contDiff_slice tr.isTrain.smooth_v hs.1
  have hg : ContDiff ℝ ∞ (fun x => tr.v s x k) :=
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hv
  have hw := (cylJetWord_proof (fun x => tr.v s x k) hg w.length z).1 w rfl
  have hcomp : ‖iteratedFDeriv ℝ w.length (fun x => tr.v s x k) z‖ ≤
      ‖iteratedFDeriv ℝ w.length (tr.v s) z‖ := by
    have h := ContinuousLinearMap.norm_iteratedFDeriv_comp_left
      (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
      (f := tr.v s) (x := z) (n := w.length) hv.contDiffAt hj
    calc ‖iteratedFDeriv ℝ w.length (fun x => tr.v s x k) z‖
        = ‖iteratedFDeriv ℝ w.length
            ((EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) ∘ tr.v s) z‖ := rfl
      _ ≤ ‖(EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)‖ *
            ‖iteratedFDeriv ℝ w.length (tr.v s) z‖ := h
      _ ≤ 1 * ‖iteratedFDeriv ℝ w.length (tr.v s) z‖ :=
            mul_le_mul_of_nonneg_right hproj (norm_nonneg _)
      _ = ‖iteratedFDeriv ℝ w.length (tr.v s) z‖ := one_mul _
  have hbound := hM0 s hs z
  show |B0151.derivWord w (fun x => tr.v s x k) z| ≤ M0
  calc |B0151.derivWord w (fun x => tr.v s x k) z|
      ≤ ‖Train.jet w.length (fun x => tr.v s x k) z‖ := hw
    _ = ‖iteratedFDeriv ℝ w.length (fun x => tr.v s x k) z‖ := rfl
    _ ≤ ‖iteratedFDeriv ℝ w.length (tr.v s) z‖ := hcomp
    _ ≤ M0 := hbound

/-- Continuous integrands with the transverse cutoff are integrable on the cell. -/
theorem vjl_cutoff_integrable {c R : ℝ} (hR : 0 < R) {g : Plane → ℝ} (hg : Continuous g) :
    IntegrableOn (fun z => etaCutoff R z.2 * g z) (Cyl.cell c) :=
  cellIntegrable_aux c R _ ((cehd_eta_cont R).mul hg)
    (fun z hz => by simp [cehd_eta_zero R z.2 hR hz])

/-! ### Step 1: the vorticity words are in `L²` -/

theorem vjl_datum_vortWord_memLp (h1 : TrainDatumWordL2) {ν c : ℝ} (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (u : List Bool) :
    MemLp (vortWord tr u 0) 2 (Cyl.cellμ c) := by
  have e : vortWord tr u 0 = fun z => wordComp (u ++ [true]) (B0140.trainDatum c) 1 z -
      wordComp (u ++ [false]) (B0140.trainDatum c) 0 z := by
    funext z
    rw [vortWord_eq tr le_rfl u z, tr.isTrain.initial]
  rw [e]
  exact (h1 c hc _ 1).sub (h1 c hc _ 0)

theorem vjl_vortWord_memLp (h1 : TrainDatumWordL2) (h2 : VortJetEnergyIneq)
    (h3 : CutoffGronwall) (h4 : CutoffL2OfBound) {ν c : ℝ} (hν : 0 < ν) (hc : 1 ≤ c)
    {tr : B0140.TrainSol ν c} (htr : IsBUCTrain tr) {s : ℝ} (hs : 0 < s) (u : List Bool) :
    MemLp (vortWord tr u s) 2 (Cyl.cellμ c) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨C, hC, hE⟩ := h2 ν c hν hc tr htr u.length s hs
  have hint0 : ∀ u' : List Bool,
      Integrable (fun z => vortWord tr u' 0 z ^ 2) (volume.restrict (Cyl.cell c)) :=
    fun u' => (vjl_datum_vortWord_memLp h1 hc0 tr u').integrable_sq
  have hsum0 : Integrable (fun z => ∑ u' ∈ wordsUpTo u.length, vortWord tr u' 0 z ^ 2)
      (volume.restrict (Cyl.cell c)) :=
    integrable_finset_sum _ (fun u' _ => hint0 u')
  have hbound : ∀ R : ℝ, 1 ≤ R →
      ∫ z in Cyl.cell c, etaCutoff R z.2 * vortWord tr u s z ^ 2 ≤
        ((∫ z in Cyl.cell c, ∑ u' ∈ wordsUpTo u.length, vortWord tr u' 0 z ^ 2) + 1) *
          Real.exp (C * s) := by
    intro R hR
    have hR0 : 0 < R := by linarith
    obtain ⟨hcont, hder⟩ := hE R hR
    have hG := h3 (vortJetEnergy tr u.length R) s C hs hC hcont hder s ⟨hs.le, le_rfl⟩
    have hz : vortJetEnergy tr u.length R 0 ≤
        ∫ z in Cyl.cell c, ∑ u' ∈ wordsUpTo u.length, vortWord tr u' 0 z ^ 2 := by
      unfold vortJetEnergy
      apply integral_mono_of_nonneg _ hsum0
      · refine Filter.Eventually.of_forall (fun z => ?_)
        have hS : 0 ≤ ∑ u' ∈ wordsUpTo u.length, vortWord tr u' 0 z ^ 2 :=
          Finset.sum_nonneg (fun _ _ => sq_nonneg _)
        have h := cehd_eta_le_one R z.2
        have h' := etaCutoff_nonneg R z.2
        show etaCutoff R z.2 * ∑ u' ∈ wordsUpTo u.length, vortWord tr u' 0 z ^ 2 ≤
          ∑ u' ∈ wordsUpTo u.length, vortWord tr u' 0 z ^ 2
        nlinarith
      · refine Filter.Eventually.of_forall (fun z => ?_)
        show (0 : ℝ) ≤ etaCutoff R z.2 * ∑ u' ∈ wordsUpTo u.length, vortWord tr u' 0 z ^ 2
        exact mul_nonneg (etaCutoff_nonneg R z.2) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    have hexp : 0 < Real.exp (C * s) := Real.exp_pos _
    have hFs : vortJetEnergy tr u.length R s ≤
        ((∫ z in Cyl.cell c, ∑ u' ∈ wordsUpTo u.length, vortWord tr u' 0 z ^ 2) + 1) *
          Real.exp (C * s) :=
      hG.trans (mul_le_mul_of_nonneg_right (by linarith) hexp.le)
    have hcs : Continuous (vortWord tr u s) := (vjl_vortWord_contDiff tr hs.le u).continuous
    have hsumc : Continuous (fun z => ∑ u' ∈ wordsUpTo u.length, vortWord tr u' s z ^ 2) :=
      continuous_finset_sum _ (fun u' _ => (vjl_vortWord_contDiff tr hs.le u').continuous.pow 2)
    have hle : ∫ z in Cyl.cell c, etaCutoff R z.2 * vortWord tr u s z ^ 2 ≤
        vortJetEnergy tr u.length R s := by
      unfold vortJetEnergy
      refine integral_mono (vjl_cutoff_integrable hR0 (hcs.pow 2))
        (vjl_cutoff_integrable hR0 hsumc) (fun z => ?_)
      refine mul_le_mul_of_nonneg_left ?_ (etaCutoff_nonneg R z.2)
      exact Finset.single_le_sum (f := fun u' => vortWord tr u' s z ^ 2)
        (fun _ _ => sq_nonneg _) (mem_wordsUpTo.2 le_rfl)
    exact hle.trans hFs
  exact h4 c _ (vortWord tr u s) hc0 (vjl_vortWord_contDiff tr hs.le u).continuous hbound

/-! ### Step 2: the velocity words are in `L²` -/

theorem vjl_base_memLp {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s) (k : Fin 2) :
    MemLp (wordComp [] (tr.v s) k) 2 (Cyl.cellμ c) := by
  have hcont : Continuous (fun x => tr.v s x k) := (vjl_slice_smooth tr hs k).continuous
  have hE : Integrable (fun z => ‖tr.v s z‖ ^ 2) (Cyl.cellμ c) :=
    tr.isTrain.finite_energy s hs
  show MemLp (fun x => tr.v s x k) 2 (Cyl.cellμ c)
  rw [memLp_two_iff_integrable_sq hcont.aestronglyMeasurable]
  refine hE.mono' (hcont.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall (fun z => ?_))
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have h1 : |tr.v s z k| ≤ ‖tr.v s z‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (tr.v s z) k
  have h2 : |tr.v s z k| ^ 2 ≤ ‖tr.v s z‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  rwa [sq_abs] at h2

theorem vjl_word_periodic {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (w : List Bool) (k : Fin 2) : Cyl.IsPeriodic c (wordComp w (tr.v s) k) := by
  have hp0 : B0151.IsPeriodicQ c (fun x => tr.v s x k) := fun q η =>
    congrArg (fun v : Vec => v k) (tr.isTrain.periodic_v s hs (q, η))
  have hp := B0151.periodic_derivWord hp0 w
  intro z
  exact hp z.1 z.2

/-- **`TrainVelocityJetL2` from the leaves.** -/
theorem trainVelocityJetL2_of (h1 : TrainDatumWordL2) (h2 : VortJetEnergyIneq)
    (h3 : CutoffGronwall) (h4 : CutoffL2OfBound) (h5 : GradL2OfLapL2)
    (h6 : TrainVelocityWordLap) : TrainVelocityJetL2 := by
  intro ν c hν hc tr htr s hs _hac w
  have hc0 : 0 < c := by linarith
  induction w with
  | nil => exact fun k => vjl_base_memLp tr hs.le k
  | cons β w' ih =>
    intro k
    have hlapk : ∀ k' : Fin 2,
        MemLp (Train.lapS (wordComp w' (tr.v s) k')) 2 (Cyl.cellμ c) := by
      intro k'
      rcases (show k' = 0 ∨ k' = 1 by fin_cases k' <;> simp) with rfl | rfl
      · have e : Train.lapS (wordComp w' (tr.v s) 0) = fun z => -vortWord tr (false :: w') s z :=
          funext fun z => (h6 ν c hc0 tr s hs.le w' z).1
        rw [e]
        exact (vjl_vortWord_memLp h1 h2 h3 h4 hν hc htr hs (false :: w')).neg
      · have e : Train.lapS (wordComp w' (tr.v s) 1) = vortWord tr (true :: w') s :=
          funext fun z => (h6 ν c hc0 tr s hs.le w' z).2
        rw [e]
        exact vjl_vortWord_memLp h1 h2 h3 h4 hν hc htr hs (true :: w')
    have hsm : ContDiff ℝ ∞ (wordComp w' (tr.v s) k) :=
      B0151.contDiff_derivWord (vjl_slice_smooth tr hs.le k) w'
    have hbd : ∃ M : ℝ, ∀ z : Plane, |wordComp w' (tr.v s) k z| ≤ M ∧
        |Cyl.partialQ (wordComp w' (tr.v s) k) z| ≤ M ∧
        |Cyl.partialEta (wordComp w' (tr.v s) k) z| ≤ M := by
      obtain ⟨M1, hM1⟩ := vjl_wordBoundedOn htr hs.le w' k
      obtain ⟨M2, hM2⟩ := vjl_wordBoundedOn htr hs.le (true :: w') k
      obtain ⟨M3, hM3⟩ := vjl_wordBoundedOn htr hs.le (false :: w') k
      have hsI : s ∈ Icc (0 : ℝ) s := ⟨hs.le, le_rfl⟩
      refine ⟨max M1 (max M2 M3), fun z => ⟨?_, ?_, ?_⟩⟩
      · exact (hM1 s hsI z).trans (le_max_left _ _)
      · exact (hM2 s hsI z).trans ((le_max_left _ _).trans (le_max_right _ _))
      · exact (hM3 s hsI z).trans ((le_max_right _ _).trans (le_max_right _ _))
    obtain ⟨hQ, hE⟩ := h5 c (wordComp w' (tr.v s) k) hc0 hsm
      (vjl_word_periodic tr hs.le w' k) hbd (ih k) (hlapk k)
    cases β
    · exact hE
    · exact hQ

end UnforcedLeray.Short.PartI
