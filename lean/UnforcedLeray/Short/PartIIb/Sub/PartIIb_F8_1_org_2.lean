import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org

/-!
# Part II-b, Sub `PartII-b_F8_1_org_2`: reduction of `CylOseenOrbitExists` (`PartII-b:F8/1/org/2`)
(`CylOseenOrbitExists`, SP 270–288, 2052–2053, 2213–2217, 2296–2301)

Source of record: `the November 2 reference manuscript`
(SP), lines 270–288 (`IsBUCTrain`), 2052–2053 (`short-bg:train-uniform`), 2213–2217
(`short-bg:body-eq` with `g = 0`), and 2296–2301 (`S_0(t, s)` on `C_c = (ℝ/cℤ) × ℝ`).

This file reduces `CylOseenOrbitExists` unconditionally (composed in task `PartII-b:F8/1/org/2` in
`OrbitExists.lean`) to three self-contained real-valued `[0, 2]` periodic-cylinder PDE leaves:

1. **Shifted BUC drift extraction (`F8Ex.isSmoothBUCDrift_shiftedDriftTrain`,
   `F8Ex.isSmoothBUCDrift_shiftedDrift`)**: from `tr : B0140.TrainSol ν c` with
   `PartI.IsBUCTrain tr` and `0 ≤ σ`, `V(s, y) = tr.v (σ + s) y` is jointly `C^∞` on
   `[0, 2] × ℝ²`, `c`-periodic in `q`, pointwise divergence-free on `[0, 2]`, and satisfies
   uniform spatial derivative bounds `∀ k : ℕ, ∃ M ≥ 0, ∀ s ∈ [0, 2], ∀ y, ‖D^k (V s)(y)‖ ≤ M`.
2. **Real/imaginary decoupling (`CMerid ≃ RMerid ⊕ i RMerid`)**:
   - `F8Ex.split_cylH1Datum`: splits any complex `F8U.IsCylH1Datum c u uq uη` into real and imaginary
     real solenoidal `H¹_σ(C_c)` data `F8Ex.IsRealCylH1Datum c`;
   - `F8Ex.recombine_normalized_orbit`: recombines two real normalized `(0, 2)` Oseen orbits
     `W_re, W_im : F8Ex.RProf` into a complex normalized `(0, 2)` Oseen orbit
     `W = ofRealMerid ∘ W_re + ofImagMerid ∘ W_im`.
3. **Initial-trace transfer (`F8Ex.realNormalizedOrbit_of_weak_and_reg`)** and **slice-to-joint
   chain-rule bridge (`F8Ex.isRealInteriorSmoothOrbit_of_joint`, `F8Ex.weak_eq_sub_of_slices`)**:
   - deduces the `s → 0⁺` `H¹(cell)` initial trace unconditionally from `C([0, 2]; H¹_σ)` weak
     continuity;
   - identifies space-time partial derivatives `pdIterR α (fun x => w x.1 x.2)` on `(0, 2) × ℝ²`
     with slice partial derivatives `slicePdIterR α (w s)` once joint `C^∞` regularity holds, and
     transfers the `[a, t]` weak pairing identity onto the spatially smooth version `w`.
4. **Age-shift equivalence `[0, 2] ↔ [σ, σ + 2]` (`F8Ex.shift_orbit_from_zero`)**: translates a
   normalized complex `(0, 2)` orbit `W` along `w(τ, y) := W(τ - σ, y)` to a full
   `F8U.IsCylOseenOrbit p σ w u uq uη` on `(σ, σ + 2) × ℝ²`.
5. **Conditional assembly (`cylOseenOrbitExists_of_leaves`, composed in `PartII-b:F8/1/org/2`)**:
   proves `CylOseenOrbitExists` from `RealCylOseenWeakH1Exists` (`PartII-b:F8/1/org/2/1`),
   `RealCylOseenSpatialBootstrap` (`PartII-b:F8/1/org/2/2`), and
   `RealCylOseenJointSmoothUpgrade` (`PartII-b:F8/1/org/2/3`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

namespace F8Ex

/-! ## 1. Real meridional profiles, shifted BUC drift on `[0, 2]`, and real PDE predicates -/

/-- Real meridional vector `(w_r, w_z) ∈ ℝ²` (`EuclideanSpace ℝ (Fin 2)`). -/
abbrev RMerid : Type := UnforcedLeray.Train.Vec

/-- A real meridional space-time profile on `Coord = ℝ × (ℝ × ℝ)`. -/
abbrev RProf : Type := Coord → RMerid

/-- Restricted Lebesgue measure on the fundamental cell `B0579.cell c = [-c/2, c/2) × ℝ`. -/
abbrev cellMeas (c : ℝ) : Measure B0579.Plane := volume.restrict (B0579.cell c)

/-- Classical spatial partial derivative `∂_q W` (`i = 0`) or `∂_η W` (`i = 1`) of a real profile. -/
def pdR (i : Fin 2) (W : RProf) (x : Coord) : RMerid := fderiv ℝ W x (F8U.sdir i)

/-- Classical age derivative `∂_s W` of a real profile. -/
def psR (W : RProf) (x : Coord) : RMerid := fderiv ℝ W x (1, (0, 0))

/-- Iterated spatial derivative `∂^α W` of a real profile for `α : Fin n → Fin 2`. -/
def pdIterR : {n : ℕ} → (Fin n → Fin 2) → RProf → RProf
  | 0, _, W => W
  | n + 1, α, W => pdR (α 0) (pdIterR (n := n) (Fin.tail α) W)

/-- Slice `y ↦ W(s, y)` of a real profile at age `s`. -/
def sliceR (W : RProf) (s : ℝ) : B0579.Plane → RMerid := fun y => W (s, y)

/-- Real `L²(cell)` norm on `B0579.cell c`. -/
def cellL2R (c : ℝ) (f : B0579.Plane → RMerid) : ℝ≥0∞ :=
  eLpNorm f 2 (cellMeas c)

/-- Real `H¹(C_c)` slice norm `‖u‖_{L²(cell)} + ‖u_q‖_{L²(cell)} + ‖u_η‖_{L²(cell)}`. -/
def cylH1R (c : ℝ) (u uq uη : B0579.Plane → RMerid) : ℝ≥0∞ :=
  cellL2R c u + cellL2R c uq + cellL2R c uη

/-- Distributional derivative on `C_c` for real scalar fields against cylinder test functions. -/
def HasWeakCellDerivR (c : ℝ) (j : Fin 2) (φ g : B0579.Plane → ℝ) : Prop :=
  (∀ ψ, B0579.IsCylTest c ψ →
    IntegrableOn (fun y => φ y * B0579.pd j ψ y) (B0579.cell c) ∧
      IntegrableOn (fun y => g y * ψ y) (B0579.cell c)) ∧
  ∀ ψ, B0579.IsCylTest c ψ →
    ∫ y in B0579.cell c, φ y * B0579.pd j ψ y = -∫ y in B0579.cell c, g y * ψ y

/-- Weak solenoidality on `C_c` for real meridional fields. -/
def IsRealCellSolenoidal (c : ℝ) (f : B0579.Plane → RMerid) : Prop :=
  ∀ ψ, B0579.IsCylTest c ψ →
    IntegrableOn (fun y => f y 0 * B0579.pd 0 ψ y + f y 1 * B0579.pd 1 ψ y) (B0579.cell c) ∧
      ∫ y in B0579.cell c, (f y 0 * B0579.pd 0 ψ y + f y 1 * B0579.pd 1 ψ y) = 0

/-- A real `H¹_σ(C_c)` datum `(u, u_q, u_η)` on the periodic cylinder `C_c`. -/
structure IsRealCylH1Datum (c : ℝ) (u uq uη : B0579.Plane → RMerid) : Prop where
  weak_q : ∀ k : Fin 2, HasWeakCellDerivR c 0 (fun y => u y k) (fun y => uq y k)
  weak_eta : ∀ k : Fin 2, HasWeakCellDerivR c 1 (fun y => u y k) (fun y => uη y k)
  solenoidal : IsRealCellSolenoidal c u
  memL2 : MemLp u 2 (cellMeas c) ∧ MemLp uq 2 (cellMeas c) ∧ MemLp uη 2 (cellMeas c)

/-- Unprojected real Oseen convective-stretching slice `(v · ∇_{q,η}) w + (w · ∇_{q,η}) v`. -/
def realBvSlice (v : B0579.Plane → RMerid) (w wq wη : B0579.Plane → RMerid)
    (y : B0579.Plane) : RMerid :=
  WithLp.toLp 2 fun i : Fin 2 =>
    v y 0 * wq y i + v y 1 * wη y i +
      w y 0 * fderiv ℝ (fun z => v z i) y ((1 : ℝ), (0 : ℝ)) +
      w y 1 * fderiv ℝ (fun z => v z i) y ((0 : ℝ), (1 : ℝ))

/-- Real homogeneous Oseen residual `∂_s W - ν(∂_q² + ∂_η²) W + B_{V(s)} W` at `x = (s, y)`. -/
def realHomResidual (ν : ℝ) (V : ℝ → B0579.Plane → RMerid) (W : RProf) (x : Coord) : RMerid :=
  psR W x - ν • (pdR 0 (pdR 0 W) x + pdR 1 (pdR 1 W) x) +
    realBvSlice (V x.1) (sliceR W x.1) (sliceR (pdR 0 W) x.1) (sliceR (pdR 1 W) x.1) x.2

/-- A smooth, `c`-periodic, divergence-free real drift `V` on `[0, 2] × ℝ²` with all spatial
derivatives uniformly bounded on `[0, 2] × ℝ²` (`BgRegime.train_buc` shifted to `[0, 2]`). -/
structure IsSmoothBUCDrift (c : ℝ) (V : ℝ → B0579.Plane → RMerid) : Prop where
  smooth : ContDiffOn ℝ ∞ (fun x : Coord => V x.1 x.2) (Icc (0 : ℝ) 2 ×ˢ univ)
  periodic : ∀ s ∈ Icc (0 : ℝ) 2, UnforcedLeray.Cyl.IsPeriodic c (V s)
  solenoidal : ∀ s ∈ Icc (0 : ℝ) 2, ∀ y : B0579.Plane,
    UnforcedLeray.Cyl.divergence (V s) y = 0
  deriv_bound : ∀ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧
    ∀ s ∈ Icc (0 : ℝ) 2, ∀ y : B0579.Plane, ‖iteratedFDeriv ℝ k (V s) y‖ ≤ M

/-- Age-shifted velocity `V(s, y) = tr.v (σ + s) y` for any train `tr : B0140.TrainSol ν c`. -/
def shiftedDriftTrain {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (σ : ℝ) :
    ℝ → B0579.Plane → RMerid :=
  fun s y => tr.v (σ + s) y

/-- Age-shifted background train velocity `V(s, y) = p.train.v (σ + s) y`. -/
def shiftedDrift (p : Params) (σ : ℝ) : ℝ → B0579.Plane → RMerid :=
  shiftedDriftTrain p.train σ

lemma isSmoothBUCDrift_shiftedDriftTrain {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hbuc : UnforcedLeray.Short.PartI.IsBUCTrain tr) {σ : ℝ} (hσ : 0 ≤ σ) :
    IsSmoothBUCDrift c (shiftedDriftTrain tr σ) where
  smooth := by
    let sh : Coord → ℝ × UnforcedLeray.Cyl.Plane := fun x => (σ + x.1, x.2)
    have hsh : ContDiff ℝ ∞ sh := (contDiff_const.add contDiff_fst).prodMk contDiff_snd
    exact tr.isTrain.smooth_v.comp hsh.contDiffOn
      (fun x hx => ⟨mem_Ici.2 (by dsimp [sh]; linarith [hx.1.1]), mem_univ _⟩)
  periodic s hs := tr.isTrain.periodic_v (σ + s) (by linarith [hs.1])
  solenoidal s hs := tr.isTrain.solenoidal (σ + s) (by linarith [hs.1])
  deriv_bound k := by
    have hS2 : 0 ≤ σ + 2 := by linarith
    obtain ⟨M₀, hM₀⟩ := hbuc.deriv_bound (hS := hS2) k
    refine ⟨max M₀ 0, le_max_right M₀ 0, fun s hs y => ?_⟩
    exact (hM₀ (σ + s) ⟨by linarith [hs.1], by linarith [hs.2]⟩ y).trans (le_max_left M₀ 0)

lemma isSmoothBUCDrift_shiftedDrift {dm dp : ℝ} {p : Params} {d : ℝ}
    (hreg : BgRegime p d dm dp) {σ : ℝ} (hσ : 0 ≤ σ) :
    IsSmoothBUCDrift p.c (shiftedDrift p σ) :=
  isSmoothBUCDrift_shiftedDriftTrain p.train hreg.train_buc hσ

/-- Smooth `c`-periodic compactly-axial-supported divergence-free real test vector field on `C_c`. -/
structure IsRealSolCylTest (c : ℝ) (Φ : B0579.Plane → RMerid) : Prop where
  cyl_test : ∀ k : Fin 2, B0579.IsCylTest c (fun y => Φ y k)
  div_free : ∀ y : B0579.Plane, UnforcedLeray.Cyl.divergence Φ y = 0

/-- Weak/mild `C([0, 2]; H¹_σ(C_c))` solution `(W, Wq, Wη)` of the real periodic-cylinder Oseen
equation `∂_s W - ν Δ W + P_0 B_{V(s)} W = 0` on `[0, 2]` with initial datum `(u, uq, uη)`. -/
structure IsRealWeakH1OseenSol (c ν : ℝ) (V : ℝ → B0579.Plane → RMerid)
    (W Wq Wη : ℝ → B0579.Plane → RMerid)
    (u uq uη : B0579.Plane → RMerid) : Prop where
  slice_h1 : ∀ s ∈ Icc (0 : ℝ) 2, IsRealCylH1Datum c (W s) (Wq s) (Wη s)
  init_eq : W 0 = u ∧ Wq 0 = uq ∧ Wη 0 = uη
  cont_h1 : ∀ s ∈ Icc (0 : ℝ) 2,
    Tendsto (fun t => cylH1R c (fun y => W t y - W s y)
      (fun y => Wq t y - Wq s y) (fun y => Wη t y - Wη s y))
      (𝓝[Icc (0 : ℝ) 2] s) (𝓝 0)
  weak_eq : ∀ Φ : B0579.Plane → RMerid, IsRealSolCylTest c Φ →
    ∀ t ∈ Icc (0 : ℝ) 2,
      IntervalIntegrable (fun r => ∫ y in B0579.cell c,
        (ν * (∑ k : Fin 2, (B0579.pd 0 (fun z => Φ z k) y * Wq r y k +
            B0579.pd 1 (fun z => Φ z k) y * Wη r y k)) +
          inner ℝ (Φ y) (realBvSlice (V r) (W r) (Wq r) (Wη r) y))) volume 0 t ∧
      (∫ y in B0579.cell c, inner ℝ (Φ y) (W t y - u y)) +
        ∫ r in (0 : ℝ)..t, ∫ y in B0579.cell c,
          (ν * (∑ k : Fin 2, (B0579.pd 0 (fun z => Φ z k) y * Wq r y k +
              B0579.pd 1 (fun z => Φ z k) y * Wη r y k)) +
            inner ℝ (Φ y) (realBvSlice (V r) (W r) (Wq r) (Wη r) y)) = 0

/-- Interior-smoothed classical real Oseen version `W_reg` on `(0, 2) × ℝ²` of a weak `H¹_σ`
solution `(W, Wq, Wη)` (the `s → 0⁺` trace is deduced unconditionally below from `cont_h1`). -/
structure IsRealInteriorSmoothOrbit (c ν : ℝ) (V : ℝ → B0579.Plane → RMerid)
    (W_reg : RProf) (W Wq Wη : ℝ → B0579.Plane → RMerid) : Prop where
  ae_val : ∀ s ∈ Ioo (0 : ℝ) 2, sliceR W_reg s =ᵐ[cellMeas c] W s
  ae_dq : ∀ s ∈ Ioo (0 : ℝ) 2, sliceR (pdR 0 W_reg) s =ᵐ[cellMeas c] Wq s
  ae_deta : ∀ s ∈ Ioo (0 : ℝ) 2, sliceR (pdR 1 W_reg) s =ᵐ[cellMeas c] Wη s
  smooth : ContDiffOn ℝ ∞ W_reg (Ioo (0 : ℝ) 2 ×ˢ univ)
  periodic : ∀ x : Coord, x.1 ∈ Ioo (0 : ℝ) 2 → W_reg (qShift c x) = W_reg x
  div_free : ∀ x : Coord, x.1 ∈ Ioo (0 : ℝ) 2 → pdR 0 W_reg x 0 + pdR 1 W_reg x 1 = 0
  memL2 : ∀ s ∈ Ioo (0 : ℝ) 2, ∀ n : ℕ, n ≤ 4 → ∀ α : Fin n → Fin 2,
    MemLp (sliceR (pdIterR α W_reg) s) 2 (cellMeas c)
  memL2_s : ∀ s ∈ Ioo (0 : ℝ) 2, ∀ n : ℕ, n ≤ 2 → ∀ α : Fin n → Fin 2,
    MemLp (sliceR (psR (pdIterR α W_reg)) s) 2 (cellMeas c)
  cont : ∀ s ∈ Ioo (0 : ℝ) 2, ∀ n : ℕ, n ≤ 4 → ∀ α : Fin n → Fin 2,
    Tendsto (fun t => cellL2R c (fun y => pdIterR α W_reg (t, y) - pdIterR α W_reg (s, y)))
      (𝓝 s) (𝓝 0)
  cont_s : ∀ s ∈ Ioo (0 : ℝ) 2, ∀ n : ℕ, n ≤ 2 → ∀ α : Fin n → Fin 2,
    Tendsto (fun t =>
      cellL2R c (fun y => psR (pdIterR α W_reg) (t, y) - psR (pdIterR α W_reg) (s, y)))
      (𝓝 s) (𝓝 0)
  projected : ∀ s ∈ Ioo (0 : ℝ) 2, ∀ φ : B0579.Plane → RMerid,
    MemLp φ 2 (cellMeas c) → IsRealCellSolenoidal c φ →
      ∫ y in B0579.cell c, inner ℝ (φ y) (realHomResidual ν V W_reg (s, y)) = 0

/-- Full real normalized Oseen orbit on `(0, 2) × ℝ²` including the `s → 0⁺` `H¹(C_c)` trace. -/
structure IsRealNormalizedOseenOrbit (c ν : ℝ) (V : ℝ → B0579.Plane → RMerid)
    (W : RProf) (u uq uη : B0579.Plane → RMerid) : Prop where
  smooth : ContDiffOn ℝ ∞ W (Ioo (0 : ℝ) 2 ×ˢ univ)
  periodic : ∀ x : Coord, x.1 ∈ Ioo (0 : ℝ) 2 → W (qShift c x) = W x
  div_free : ∀ x : Coord, x.1 ∈ Ioo (0 : ℝ) 2 → pdR 0 W x 0 + pdR 1 W x 1 = 0
  memL2 : ∀ s ∈ Ioo (0 : ℝ) 2, ∀ n : ℕ, n ≤ 4 → ∀ α : Fin n → Fin 2,
    MemLp (sliceR (pdIterR α W) s) 2 (cellMeas c)
  memL2_s : ∀ s ∈ Ioo (0 : ℝ) 2, ∀ n : ℕ, n ≤ 2 → ∀ α : Fin n → Fin 2,
    MemLp (sliceR (psR (pdIterR α W)) s) 2 (cellMeas c)
  cont : ∀ s ∈ Ioo (0 : ℝ) 2, ∀ n : ℕ, n ≤ 4 → ∀ α : Fin n → Fin 2,
    Tendsto (fun t => cellL2R c (fun y => pdIterR α W (t, y) - pdIterR α W (s, y)))
      (𝓝 s) (𝓝 0)
  cont_s : ∀ s ∈ Ioo (0 : ℝ) 2, ∀ n : ℕ, n ≤ 2 → ∀ α : Fin n → Fin 2,
    Tendsto (fun t => cellL2R c (fun y => psR (pdIterR α W) (t, y) - psR (pdIterR α W) (s, y)))
      (𝓝 s) (𝓝 0)
  projected : ∀ s ∈ Ioo (0 : ℝ) 2, ∀ φ : B0579.Plane → RMerid,
    MemLp φ 2 (cellMeas c) → IsRealCellSolenoidal c φ →
      ∫ y in B0579.cell c, inner ℝ (φ y) (realHomResidual ν V W (s, y)) = 0
  initial : Tendsto (fun t => cylH1R c (fun y => W (t, y) - u y)
      (fun y => pdR 0 W (t, y) - uq y) (fun y => pdR 1 W (t, y) - uη y))
      (𝓝[>] (0 : ℝ)) (𝓝 0)

/-! ## 2. Unconditional `s → 0⁺` initial-trace transfer from weak `H¹` continuity -/

lemma realNormalizedOrbit_of_weak_and_reg {c ν : ℝ} {V : ℝ → B0579.Plane → RMerid}
    {W Wq Wη : ℝ → B0579.Plane → RMerid} {u uq uη : B0579.Plane → RMerid} {W_reg : RProf}
    (hwk : IsRealWeakH1OseenSol c ν V W Wq Wη u uq uη)
    (hreg : IsRealInteriorSmoothOrbit c ν V W_reg W Wq Wη) :
    IsRealNormalizedOseenOrbit c ν V W_reg u uq uη where
  smooth := hreg.smooth
  periodic := hreg.periodic
  div_free := hreg.div_free
  memL2 := hreg.memL2
  memL2_s := hreg.memL2_s
  cont := hreg.cont
  cont_s := hreg.cont_s
  projected := hreg.projected
  initial := by
    have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 2 := ⟨le_rfl, by norm_num⟩
    have hlim0 := hwk.cont_h1 0 h0
    rw [hwk.init_eq.1, hwk.init_eq.2.1, hwk.init_eq.2.2] at hlim0
    have hev_Ioo : Ioo (0 : ℝ) 2 ∈ 𝓝[>] (0 : ℝ) :=
      Filter.inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num)))
    have hmono : Tendsto id (𝓝[>] (0 : ℝ)) (𝓝[Icc (0 : ℝ) 2] (0 : ℝ)) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_id.mono_left nhdsWithin_le_nhds,
        Filter.Eventually.mono hev_Ioo fun t ht => ⟨ht.1.le, ht.2.le⟩⟩
    refine (hlim0.comp hmono).congr' ?_
    filter_upwards [hev_Ioo] with t ht
    have e0 : cellL2R c (fun y => W t y - u y) = cellL2R c (fun y => W_reg (t, y) - u y) :=
      eLpNorm_congr_ae ((hreg.ae_val t ht).symm.sub (EventuallyEq.refl _ u))
    have e1 : cellL2R c (fun y => Wq t y - uq y) =
        cellL2R c (fun y => pdR 0 W_reg (t, y) - uq y) :=
      eLpNorm_congr_ae ((hreg.ae_dq t ht).symm.sub (EventuallyEq.refl _ uq))
    have e2 : cellL2R c (fun y => Wη t y - uη y) =
        cellL2R c (fun y => pdR 1 W_reg (t, y) - uη y) :=
      eLpNorm_congr_ae ((hreg.ae_deta t ht).symm.sub (EventuallyEq.refl _ uη))
    dsimp only [Function.comp_apply, id_eq, cylH1R]
    rw [e0, e1, e2]

/-! ## 3. Real/imaginary continuous `ℝ`-linear maps and splitting of `IsCylH1Datum` -/

def πC (k : Fin 2) : CMerid →L[ℝ] ℂ :=
  (EuclideanSpace.proj k : CMerid →L[ℂ] ℂ).restrictScalars ℝ

def πR (k : Fin 2) : RMerid →L[ℝ] ℝ := EuclideanSpace.proj k

def eC0 : CMerid := EuclideanSpace.single (0 : Fin 2) (1 : ℂ)
def eC1 : CMerid := EuclideanSpace.single (1 : Fin 2) (1 : ℂ)
def eR0 : RMerid := EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
def eR1 : RMerid := EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

def reMerid : CMerid →L[ℝ] RMerid :=
  (Complex.reCLM.comp (πC 0)).smulRight eR0 + (Complex.reCLM.comp (πC 1)).smulRight eR1

def imMerid : CMerid →L[ℝ] RMerid :=
  (Complex.imCLM.comp (πC 0)).smulRight eR0 + (Complex.imCLM.comp (πC 1)).smulRight eR1

def ofRealMerid : RMerid →L[ℝ] CMerid :=
  (πR 0).smulRight eC0 + (πR 1).smulRight eC1

def ofImagMerid : RMerid →L[ℝ] CMerid :=
  (πR 0).smulRight (Complex.I • eC0) + (πR 1).smulRight (Complex.I • eC1)

def combineMerid (a b : RMerid) : CMerid := ofRealMerid a + ofImagMerid b

@[simp] lemma reMerid_apply (z : CMerid) (k : Fin 2) : reMerid z k = (z k).re := by
  fin_cases k <;>
    simp [reMerid, eR0, eR1, πC]

@[simp] lemma imMerid_apply (z : CMerid) (k : Fin 2) : imMerid z k = (z k).im := by
  fin_cases k <;>
    simp [imMerid, eR0, eR1, πC]

@[simp] lemma ofRealMerid_apply (v : RMerid) (k : Fin 2) : ofRealMerid v k = (v k : ℂ) := by
  fin_cases k <;>
    simp [ofRealMerid, eC0, eC1, πR]

@[simp] lemma ofImagMerid_apply (v : RMerid) (k : Fin 2) :
    ofImagMerid v k = Complex.I * (v k : ℂ) := by
  fin_cases k <;>
    simp [ofImagMerid, eC0, eC1, πR, mul_comm]

@[simp] lemma combineMerid_apply (a b : RMerid) (k : Fin 2) :
    combineMerid a b k = (a k : ℂ) + Complex.I * (b k : ℂ) := by
  simp [combineMerid]

lemma combineMerid_re_im (z : CMerid) : combineMerid (reMerid z) (imMerid z) = z := by
  ext k
  rw [combineMerid_apply, reMerid_apply, imMerid_apply, mul_comm Complex.I, Complex.re_add_im]

lemma norm_ofRealMerid (v : RMerid) : ‖ofRealMerid v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_two, Fin.sum_univ_two,
    ofRealMerid_apply, ofRealMerid_apply, Complex.norm_real, Complex.norm_real]

lemma norm_ofImagMerid (v : RMerid) : ‖ofImagMerid v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_two, Fin.sum_univ_two,
    ofImagMerid_apply, ofImagMerid_apply, norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul,
    Complex.norm_real, Complex.norm_real]

lemma cellL2_ofRealMerid {c : ℝ} (f : B0579.Plane → RMerid) :
    F8U.cellL2 c (fun y => ofRealMerid (f y)) = cellL2R c f := by
  unfold F8U.cellL2 cellL2R
  rw [← eLpNorm_norm (fun y => ofRealMerid (f y)), ← eLpNorm_norm f]
  simp only [norm_ofRealMerid]

lemma cellL2_ofImagMerid {c : ℝ} (f : B0579.Plane → RMerid) :
    F8U.cellL2 c (fun y => ofImagMerid (f y)) = cellL2R c f := by
  unfold F8U.cellL2 cellL2R
  rw [← eLpNorm_norm (fun y => ofImagMerid (f y)), ← eLpNorm_norm f]
  simp only [norm_ofImagMerid]

lemma memLp_fun_add {E : Type*} [NormedAddCommGroup E] {c : ℝ} {f g : B0579.Plane → E}
    (hf : MemLp f 2 (cellMeas c)) (hg : MemLp g 2 (cellMeas c)) :
    MemLp (fun y => f y + g y) 2 (cellMeas c) :=
  hf.add hg

lemma cellL2_combineMerid_le {c : ℝ} {a b : B0579.Plane → RMerid}
    (ha : MemLp a 2 (cellMeas c)) (hb : MemLp b 2 (cellMeas c)) :
    F8U.cellL2 c (fun y => combineMerid (a y) (b y)) ≤ cellL2R c a + cellL2R c b := by
  have hma : MemLp (fun y => ofRealMerid (a y)) 2 (cellMeas c) := ofRealMerid.comp_memLp' ha
  have hmb : MemLp (fun y => ofImagMerid (b y)) 2 (cellMeas c) := ofImagMerid.comp_memLp' hb
  calc F8U.cellL2 c (fun y => combineMerid (a y) (b y))
      ≤ F8U.cellL2 c (fun y => ofRealMerid (a y)) + F8U.cellL2 c (fun y => ofImagMerid (b y)) :=
        eLpNorm_add_le hma.aestronglyMeasurable hmb.aestronglyMeasurable one_le_two
    _ = cellL2R c a + cellL2R c b := by
        rw [cellL2_ofRealMerid, cellL2_ofImagMerid]

lemma hasWeakCellDerivR_re_im {c : ℝ} {j : Fin 2} {φ g : B0579.Plane → ℂ}
    (h : IIIa.HasWeakCellDerivC c j φ g) :
    HasWeakCellDerivR c j (fun y => (φ y).re) (fun y => (g y).re) ∧
    HasWeakCellDerivR c j (fun y => (φ y).im) (fun y => (g y).im) := by
  have hre_lhs : ∀ ψ : B0579.Plane → ℝ, (fun y => (φ y * (B0579.pd j ψ y : ℂ)).re) =
      fun y => (φ y).re * B0579.pd j ψ y := by
    intro ψ; funext y; simp [Complex.mul_re]
  have hre_rhs : ∀ ψ : B0579.Plane → ℝ, (fun y => (g y * (ψ y : ℂ)).re) =
      fun y => (g y).re * ψ y := by
    intro ψ; funext y; simp [Complex.mul_re]
  have him_lhs : ∀ ψ : B0579.Plane → ℝ, (fun y => (φ y * (B0579.pd j ψ y : ℂ)).im) =
      fun y => (φ y).im * B0579.pd j ψ y := by
    intro ψ; funext y; simp [Complex.mul_im]
  have him_rhs : ∀ ψ : B0579.Plane → ℝ, (fun y => (g y * (ψ y : ℂ)).im) =
      fun y => (g y).im * ψ y := by
    intro ψ; funext y; simp [Complex.mul_im]
  refine ⟨⟨fun ψ hψ => ?_, fun ψ hψ => ?_⟩, ⟨fun ψ hψ => ?_, fun ψ hψ => ?_⟩⟩
  · obtain ⟨i1, i2⟩ := h.1 ψ hψ
    rw [← hre_lhs ψ, ← hre_rhs ψ]
    exact ⟨Complex.reCLM.integrable_comp i1, Complex.reCLM.integrable_comp i2⟩
  · obtain ⟨i1, i2⟩ := h.1 ψ hψ
    have heq := congrArg Complex.re (h.2 ψ hψ)
    rw [Complex.neg_re] at heq
    have c1 := Complex.reCLM.integral_comp_comm i1
    have c2 := Complex.reCLM.integral_comp_comm i2
    simp only [Complex.reCLM_apply] at c1 c2
    change ∫ y in B0579.cell c, (fun z => (φ z * (B0579.pd j ψ z : ℂ)).re) y = _ at c1
    change ∫ y in B0579.cell c, (fun z => (g z * (ψ z : ℂ)).re) y = _ at c2
    rw [hre_lhs ψ] at c1
    rw [hre_rhs ψ] at c2
    dsimp only at c1 c2 ⊢
    rw [c1, c2, heq]
  · obtain ⟨i1, i2⟩ := h.1 ψ hψ
    rw [← him_lhs ψ, ← him_rhs ψ]
    exact ⟨Complex.imCLM.integrable_comp i1, Complex.imCLM.integrable_comp i2⟩
  · obtain ⟨i1, i2⟩ := h.1 ψ hψ
    have heq := congrArg Complex.im (h.2 ψ hψ)
    rw [Complex.neg_im] at heq
    have c1 := Complex.imCLM.integral_comp_comm i1
    have c2 := Complex.imCLM.integral_comp_comm i2
    simp only [Complex.imCLM_apply] at c1 c2
    change ∫ y in B0579.cell c, (fun z => (φ z * (B0579.pd j ψ z : ℂ)).im) y = _ at c1
    change ∫ y in B0579.cell c, (fun z => (g z * (ψ z : ℂ)).im) y = _ at c2
    rw [him_lhs ψ] at c1
    rw [him_rhs ψ] at c2
    dsimp only at c1 c2 ⊢
    rw [c1, c2, heq]

lemma isRealCellSolenoidal_re_im {c : ℝ} {f : B0579.Plane → CMerid}
    (hf : F8U.IsCellSolenoidal c f) :
    IsRealCellSolenoidal c (fun y => reMerid (f y)) ∧
    IsRealCellSolenoidal c (fun y => imMerid (f y)) := by
  have hre_eq : ∀ ψ : B0579.Plane → ℝ,
      (fun y => (f y 0 * (B0579.pd 0 ψ y : ℂ) + f y 1 * (B0579.pd 1 ψ y : ℂ)).re) =
      fun y => reMerid (f y) 0 * B0579.pd 0 ψ y + reMerid (f y) 1 * B0579.pd 1 ψ y := by
    intro ψ; funext y; simp [Complex.mul_re]
  have him_eq : ∀ ψ : B0579.Plane → ℝ,
      (fun y => (f y 0 * (B0579.pd 0 ψ y : ℂ) + f y 1 * (B0579.pd 1 ψ y : ℂ)).im) =
      fun y => imMerid (f y) 0 * B0579.pd 0 ψ y + imMerid (f y) 1 * B0579.pd 1 ψ y := by
    intro ψ; funext y; simp [Complex.mul_im]
  refine ⟨fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · obtain ⟨hint, hzero⟩ := hf ψ hψ
    refine ⟨?_, ?_⟩
    · rw [← hre_eq ψ]; exact Complex.reCLM.integrable_comp hint
    · have h0 := congrArg Complex.re hzero
      rw [Complex.zero_re] at h0
      have c1 := Complex.reCLM.integral_comp_comm hint
      simp only [Complex.reCLM_apply] at c1
      change ∫ y in B0579.cell c,
        (fun z => (f z 0 * (B0579.pd 0 ψ z : ℂ) + f z 1 * (B0579.pd 1 ψ z : ℂ)).re) y = _ at c1
      rw [hre_eq ψ] at c1
      dsimp only at c1 ⊢
      rw [c1, h0]
  · obtain ⟨hint, hzero⟩ := hf ψ hψ
    refine ⟨?_, ?_⟩
    · rw [← him_eq ψ]; exact Complex.imCLM.integrable_comp hint
    · have h0 := congrArg Complex.im hzero
      rw [Complex.zero_im] at h0
      have c1 := Complex.imCLM.integral_comp_comm hint
      simp only [Complex.imCLM_apply] at c1
      change ∫ y in B0579.cell c,
        (fun z => (f z 0 * (B0579.pd 0 ψ z : ℂ) + f z 1 * (B0579.pd 1 ψ z : ℂ)).im) y = _ at c1
      rw [him_eq ψ] at c1
      dsimp only at c1 ⊢
      rw [c1, h0]

lemma split_cylH1Datum {c : ℝ} {u uq uη : B0579.Plane → CMerid}
    (hdat : F8U.IsCylH1Datum c u uq uη) :
    IsRealCylH1Datum c (fun y => reMerid (u y)) (fun y => reMerid (uq y))
      (fun y => reMerid (uη y)) ∧
    IsRealCylH1Datum c (fun y => imMerid (u y)) (fun y => imMerid (uq y))
      (fun y => imMerid (uη y)) := by
  obtain ⟨hsol_re, hsol_im⟩ := isRealCellSolenoidal_re_im hdat.solenoidal
  refine ⟨⟨?_, ?_, hsol_re,
      reMerid.comp_memLp' hdat.memL2.1,
      reMerid.comp_memLp' hdat.memL2.2.1,
      reMerid.comp_memLp' hdat.memL2.2.2⟩,
    ⟨?_, ?_, hsol_im,
      imMerid.comp_memLp' hdat.memL2.1,
      imMerid.comp_memLp' hdat.memL2.2.1,
      imMerid.comp_memLp' hdat.memL2.2.2⟩⟩
  · intro k
    simpa only [reMerid_apply] using (hasWeakCellDerivR_re_im (hdat.weak_q k)).1
  · intro k
    simpa only [reMerid_apply] using (hasWeakCellDerivR_re_im (hdat.weak_eta k)).1
  · intro k
    simpa only [imMerid_apply] using (hasWeakCellDerivR_re_im (hdat.weak_q k)).2
  · intro k
    simpa only [imMerid_apply] using (hasWeakCellDerivR_re_im (hdat.weak_eta k)).2

/-! ## 4. Normalized complex `(0, 2)` Oseen orbit and recombination of real/imaginary orbits -/

abbrev strip0 : Set Coord := Ioo (0 : ℝ) 2 ×ˢ univ

lemma isOpen_strip0 : IsOpen strip0 := isOpen_Ioo.prod isOpen_univ

lemma contDiffOn_fderiv_dir {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Coord → E} (hf : ContDiffOn ℝ ∞ f strip0) (d : Coord) :
    ContDiffOn ℝ ∞ (fun x => fderiv ℝ f x d) strip0 := by
  intro x hx
  have hfa : ContDiffAt ℝ ∞ f x := hf.contDiffAt (isOpen_strip0.mem_nhds hx)
  exact ((hfa.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).contDiffWithinAt

lemma contDiffOn_pdR {W : RProf} (hW : ContDiffOn ℝ ∞ W strip0) :
    ∀ {n : ℕ} (α : Fin n → Fin 2), ContDiffOn ℝ ∞ (pdIterR α W) strip0
  | 0, _ => hW
  | _ + 1, α => contDiffOn_fderiv_dir (contDiffOn_pdR hW (Fin.tail α)) (F8U.sdir (α 0))

lemma fderiv_combineMerid {A B : RProf}
    (hA : ContDiffOn ℝ ∞ A strip0) (hB : ContDiffOn ℝ ∞ B strip0)
    {x : Coord} (hx : x ∈ strip0) (d : Coord) :
    fderiv ℝ (fun z => combineMerid (A z) (B z)) x d =
      combineMerid (fderiv ℝ A x d) (fderiv ℝ B x d) := by
  have hdA : DifferentiableAt ℝ A x :=
    (hA.contDiffAt (isOpen_strip0.mem_nhds hx)).differentiableAt (by simp)
  have hdB : DifferentiableAt ℝ B x :=
    (hB.contDiffAt (isOpen_strip0.mem_nhds hx)).differentiableAt (by simp)
  have h1 := ofRealMerid.hasFDerivAt.comp x hdA.hasFDerivAt
  have h2 := ofImagMerid.hasFDerivAt.comp x hdB.hasFDerivAt
  have hsum : HasFDerivAt (fun z => combineMerid (A z) (B z))
      (ofRealMerid.comp (fderiv ℝ A x) + ofImagMerid.comp (fderiv ℝ B x)) x :=
    h1.add h2
  rw [hsum.fderiv]
  rfl

lemma pdIter_combineMerid {A B : RProf}
    (hA : ContDiffOn ℝ ∞ A strip0) (hB : ContDiffOn ℝ ∞ B strip0) :
    ∀ {n : ℕ} (α : Fin n → Fin 2) {x : Coord}, x ∈ strip0 →
      F8U.pdIter α (fun z => combineMerid (A z) (B z)) x =
        combineMerid (pdIterR α A x) (pdIterR α B x)
  | 0, _, _, _ => rfl
  | _ + 1, α, x, hx => by
      have hev : F8U.pdIter (Fin.tail α) (fun z => combineMerid (A z) (B z)) =ᶠ[𝓝 x]
          fun z => combineMerid (pdIterR (Fin.tail α) A z) (pdIterR (Fin.tail α) B z) :=
        Filter.eventuallyEq_of_mem (isOpen_strip0.mem_nhds hx)
          fun z hz => pdIter_combineMerid hA hB (Fin.tail α) hz
      simp only [F8U.pdIter, F8U.pd, pdIterR, pdR]
      rw [hev.fderiv_eq]
      exact fderiv_combineMerid (contDiffOn_pdR hA (Fin.tail α))
        (contDiffOn_pdR hB (Fin.tail α)) hx (F8U.sdir (α 0))

lemma ps_pdIter_combineMerid {A B : RProf}
    (hA : ContDiffOn ℝ ∞ A strip0) (hB : ContDiffOn ℝ ∞ B strip0)
    {n : ℕ} (α : Fin n → Fin 2) {x : Coord} (hx : x ∈ strip0) :
    F8U.ps (F8U.pdIter α (fun z => combineMerid (A z) (B z))) x =
      combineMerid (psR (pdIterR α A) x) (psR (pdIterR α B) x) := by
  have hev : F8U.pdIter α (fun z => combineMerid (A z) (B z)) =ᶠ[𝓝 x]
      fun z => combineMerid (pdIterR α A z) (pdIterR α B z) :=
    Filter.eventuallyEq_of_mem (isOpen_strip0.mem_nhds hx)
      fun z hz => pdIter_combineMerid hA hB α hz
  unfold F8U.ps psR
  rw [hev.fderiv_eq]
  exact fderiv_combineMerid (contDiffOn_pdR hA α) (contDiffOn_pdR hB α) hx (1, (0, 0))

/-- Complex convective-stretching slice for a real drift `v`. -/
def complexBvSlice (v : B0579.Plane → RMerid) (w wq wη : B0579.Plane → CMerid)
    (y : B0579.Plane) : CMerid :=
  WithLp.toLp 2 fun i : Fin 2 =>
    ((v y 0 : ℝ) : ℂ) * wq y i + ((v y 1 : ℝ) : ℂ) * wη y i +
      w y 0 * ((fderiv ℝ (fun z => v z i) y ((1 : ℝ), (0 : ℝ)) : ℝ) : ℂ) +
      w y 1 * ((fderiv ℝ (fun z => v z i) y ((0 : ℝ), (1 : ℝ)) : ℝ) : ℂ)

/-- Complex homogeneous Oseen residual on `(0, 2)` for a general real drift `V`. -/
def normHomResidual (ν : ℝ) (V : ℝ → B0579.Plane → RMerid) (W : CProf) (x : Coord) : CMerid :=
  F8U.ps W x - ν • (F8U.pd 0 (F8U.pd 0 W) x + F8U.pd 1 (F8U.pd 1 W) x) +
    complexBvSlice (V x.1) (F8U.slice W x.1) (F8U.slice (F8U.pd 0 W) x.1)
      (F8U.slice (F8U.pd 1 W) x.1) x.2

/-- Normalized complex Oseen orbit on `(0, 2) × ℝ²` for a real drift `V`. -/
structure IsComplexNormalizedOseenOrbit (c ν : ℝ) (V : ℝ → B0579.Plane → RMerid)
    (W : CProf) (u uq uη : B0579.Plane → CMerid) : Prop where
  smooth : ContDiffOn ℝ ∞ W (Ioo (0 : ℝ) 2 ×ˢ univ)
  periodic : ∀ x : Coord, x.1 ∈ Ioo (0 : ℝ) 2 → W (qShift c x) = W x
  div_free : ∀ x : Coord, x.1 ∈ Ioo (0 : ℝ) 2 → F8U.pd 0 W x 0 + F8U.pd 1 W x 1 = 0
  memL2 : ∀ s ∈ Ioo (0 : ℝ) 2, ∀ n : ℕ, n ≤ 4 → ∀ α : Fin n → Fin 2,
    MemLp (F8U.slice (F8U.pdIter α W) s) 2 (cellMeas c)
  memL2_s : ∀ s ∈ Ioo (0 : ℝ) 2, ∀ n : ℕ, n ≤ 2 → ∀ α : Fin n → Fin 2,
    MemLp (F8U.slice (F8U.ps (F8U.pdIter α W)) s) 2 (cellMeas c)
  cont : ∀ s ∈ Ioo (0 : ℝ) 2, ∀ n : ℕ, n ≤ 4 → ∀ α : Fin n → Fin 2,
    Tendsto (fun t => F8U.cellL2 c (fun y => F8U.pdIter α W (t, y) - F8U.pdIter α W (s, y)))
      (𝓝 s) (𝓝 0)
  cont_s : ∀ s ∈ Ioo (0 : ℝ) 2, ∀ n : ℕ, n ≤ 2 → ∀ α : Fin n → Fin 2,
    Tendsto (fun t =>
      F8U.cellL2 c (fun y => F8U.ps (F8U.pdIter α W) (t, y) - F8U.ps (F8U.pdIter α W) (s, y)))
      (𝓝 s) (𝓝 0)
  projected : ∀ s ∈ Ioo (0 : ℝ) 2, ∀ φ : B0579.Plane → CMerid,
    MemLp φ 2 (cellMeas c) → F8U.IsCellSolenoidal c φ →
      ∫ y in B0579.cell c, inner ℂ (φ y) (normHomResidual ν V W (s, y)) = 0
  initial : Tendsto (fun t => F8U.cylH1 c (fun y => W (t, y) - u y)
      (fun y => F8U.pd 0 W (t, y) - uq y) (fun y => F8U.pd 1 W (t, y) - uη y))
      (𝓝[>] (0 : ℝ)) (𝓝 0)

lemma normHomResidual_combineMerid {ν : ℝ} {V : ℝ → B0579.Plane → RMerid} {A B : RProf}
    (hA : ContDiffOn ℝ ∞ A strip0) (hB : ContDiffOn ℝ ∞ B strip0)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 2) (y : B0579.Plane) :
    normHomResidual ν V (fun z => combineMerid (A z) (B z)) (s, y) =
      combineMerid (realHomResidual ν V A (s, y)) (realHomResidual ν V B (s, y)) := by
  have hx : (s, y) ∈ strip0 := ⟨hs, trivial⟩
  have hps := ps_pdIter_combineMerid hA hB ![] hx
  have hp0 := pdIter_combineMerid hA hB ![0] hx
  have hp1 := pdIter_combineMerid hA hB ![1] hx
  have hp00 := pdIter_combineMerid hA hB ![0, 0] hx
  have hp11 := pdIter_combineMerid hA hB ![1, 1] hx
  change F8U.ps (fun z => combineMerid (A z) (B z)) (s, y) =
    combineMerid (psR A (s, y)) (psR B (s, y)) at hps
  change F8U.pd 0 (fun z => combineMerid (A z) (B z)) (s, y) =
    combineMerid (pdR 0 A (s, y)) (pdR 0 B (s, y)) at hp0
  change F8U.pd 1 (fun z => combineMerid (A z) (B z)) (s, y) =
    combineMerid (pdR 1 A (s, y)) (pdR 1 B (s, y)) at hp1
  change F8U.pd 0 (F8U.pd 0 (fun z => combineMerid (A z) (B z))) (s, y) =
    combineMerid (pdR 0 (pdR 0 A) (s, y)) (pdR 0 (pdR 0 B) (s, y)) at hp00
  change F8U.pd 1 (F8U.pd 1 (fun z => combineMerid (A z) (B z))) (s, y) =
    combineMerid (pdR 1 (pdR 1 A) (s, y)) (pdR 1 (pdR 1 B) (s, y)) at hp11
  ext k
  unfold normHomResidual realHomResidual complexBvSlice realBvSlice F8U.slice sliceR
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
    hps, hp0, hp1, hp00, hp11, combineMerid_apply, Complex.real_smul,
    Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul]
  ring

lemma memLp_mulRealR {c M : ℝ} {a : B0579.Plane → ℝ} {G : B0579.Plane → RMerid}
    (ha : Continuous a) (hbdd : ∀ y, |a y| ≤ M) (hG : MemLp G 2 (cellMeas c)) :
    MemLp (fun y => a y • G y) 2 (cellMeas c) := by
  set M' := max M 0
  have hM' : 0 ≤ M' := le_max_right M 0
  have hmeas : AEStronglyMeasurable (fun y => a y • G y) (cellMeas c) :=
    ha.aestronglyMeasurable.smul hG.aestronglyMeasurable
  have hpt : ∀ y : B0579.Plane, ‖a y • G y‖ ≤ ‖M' • G y‖ := by
    intro y
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_of_nonneg hM']
    exact mul_le_mul_of_nonneg_right ((hbdd y).trans (le_max_left M 0)) (norm_nonneg _)
  have hle : eLpNorm (fun y => a y • G y) 2 (cellMeas c) ≤
      ENNReal.ofReal M' * eLpNorm G 2 (cellMeas c) := by
    calc eLpNorm (fun y => a y • G y) 2 (cellMeas c)
        ≤ eLpNorm (M' • G) 2 (cellMeas c) := eLpNorm_mono hpt
      _ = ‖M'‖ₑ * eLpNorm G 2 (cellMeas c) := eLpNorm_const_smul M' G 2 (cellMeas c)
      _ = ENNReal.ofReal M' * eLpNorm G 2 (cellMeas c) := by
          rw [← ofReal_norm, Real.norm_of_nonneg hM']
  exact ⟨hmeas, lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hG.eLpNorm_lt_top)⟩

lemma drift_slice_bounds {c : ℝ} {V : ℝ → B0579.Plane → RMerid}
    (hV : IsSmoothBUCDrift c V) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 2) :
    ∃ M : ℝ, 0 ≤ M ∧ ContDiff ℝ ∞ (V s) ∧
      (∀ k : Fin 2, ∀ y : B0579.Plane, |V s y k| ≤ M) ∧
      (∀ i k : Fin 2, ∀ y : B0579.Plane,
        |fderiv ℝ (fun z => V s z k) y (B0579.dir i)| ≤ M) := by
  have hVs : ContDiff ℝ ∞ (V s) := by
    have hc := hV.smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (s := univ) (fun y _ => ⟨hs, mem_univ y⟩)
    exact contDiffOn_univ.1 hc
  obtain ⟨M0, hM0_nn, hM0⟩ := hV.deriv_bound 0
  obtain ⟨M1, _, hM1⟩ := hV.deriv_bound 1
  refine ⟨max M0 M1, le_trans hM0_nn (le_max_left M0 M1), hVs, ?_, ?_⟩
  · intro k y
    calc |V s y k| = ‖V s y k‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖V s y‖ := PiLp.norm_apply_le (V s y) k
      _ = ‖iteratedFDeriv ℝ 0 (V s) y‖ := (norm_iteratedFDeriv_zero (f := V s) (x := y)).symm
      _ ≤ M0 := hM0 s hs y
      _ ≤ max M0 M1 := le_max_left M0 M1
  · intro i k y
    have hproj : fderiv ℝ (fun z => V s z k) y (B0579.dir i) =
        fderiv ℝ (V s) y (B0579.dir i) k := by
      have hc := ((πR k).hasFDerivAt.comp y
        (hVs.contDiffAt.differentiableAt (by simp)).hasFDerivAt).fderiv
      change fderiv ℝ ((πR k) ∘ (V s)) y (B0579.dir i) = πR k (fderiv ℝ (V s) y (B0579.dir i))
      rw [hc, ContinuousLinearMap.comp_apply]
    have hdir_norm : ‖B0579.dir i‖ = 1 := by
      fin_cases i <;> simp [B0579.dir]
    rw [hproj]
    calc |fderiv ℝ (V s) y (B0579.dir i) k|
        = ‖fderiv ℝ (V s) y (B0579.dir i) k‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ (V s) y (B0579.dir i)‖ := PiLp.norm_apply_le _ k
      _ = ‖iteratedFDeriv ℝ 1 (V s) y ![B0579.dir i]‖ := by
          rw [iteratedFDeriv_one_apply, Matrix.cons_val_zero]
      _ ≤ ‖iteratedFDeriv ℝ 1 (V s) y‖ * ∏ j : Fin 1, ‖(![B0579.dir i] : Fin 1 → B0579.Plane) j‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖iteratedFDeriv ℝ 1 (V s) y‖ := by simp [hdir_norm]
      _ ≤ M1 := hM1 s hs y
      _ ≤ max M0 M1 := le_max_right M0 M1

lemma memLp_realHomResidual {c ν : ℝ} {V : ℝ → B0579.Plane → RMerid}
    (hV : IsSmoothBUCDrift c V) {W : RProf} {u uq uη : B0579.Plane → RMerid}
    (hW : IsRealNormalizedOseenOrbit c ν V W u uq uη) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 2) :
    MemLp (fun y => realHomResidual ν V W (s, y)) 2 (cellMeas c) := by
  obtain ⟨M, _, hVs, hb0, hb1⟩ := drift_slice_bounds hV ⟨hs.1.le, hs.2.le⟩
  have hm0 : MemLp (sliceR W s) 2 (cellMeas c) := hW.memL2 s hs 0 (by decide) ![]
  have hm10 : MemLp (sliceR (pdR 0 W) s) 2 (cellMeas c) := hW.memL2 s hs 1 (by decide) ![0]
  have hm11 : MemLp (sliceR (pdR 1 W) s) 2 (cellMeas c) := hW.memL2 s hs 1 (by decide) ![1]
  have hm20 : MemLp (sliceR (pdR 0 (pdR 0 W)) s) 2 (cellMeas c) :=
    hW.memL2 s hs 2 (by decide) ![0, 0]
  have hm21 : MemLp (sliceR (pdR 1 (pdR 1 W)) s) 2 (cellMeas c) :=
    hW.memL2 s hs 2 (by decide) ![1, 1]
  have hms : MemLp (sliceR (psR W) s) 2 (cellMeas c) := hW.memL2_s s hs 0 (by decide) ![]
  have hcv0 : Continuous (fun y => V s y 0) := (πR 0).continuous.comp hVs.continuous
  have hcv1 : Continuous (fun y => V s y 1) := (πR 1).continuous.comp hVs.continuous
  have mt0 : MemLp (fun y => V s y 0 • sliceR (pdR 0 W) s y) 2 (cellMeas c) :=
    memLp_mulRealR hcv0 (hb0 0) hm10
  have mt1 : MemLp (fun y => V s y 1 • sliceR (pdR 1 W) s y) 2 (cellMeas c) :=
    memLp_mulRealR hcv1 (hb0 1) hm11
  let dV (j : Fin 2) : B0579.Plane → RMerid := fun y => fderiv ℝ (V s) y (B0579.dir j)
  have hcdV (j : Fin 2) : Continuous (dV j) :=
    ((contDiff_infty_iff_fderiv.1 hVs).2.clm_apply contDiff_const).continuous
  have hdV_eq (j i : Fin 2) (y : B0579.Plane) :
      fderiv ℝ (fun z => V s z i) y (B0579.dir j) = dV j y i := by
    have hc := ((πR i).hasFDerivAt.comp y
      (hVs.contDiffAt.differentiableAt (by simp)).hasFDerivAt).fderiv
    change fderiv ℝ ((πR i) ∘ (V s)) y (B0579.dir j) = πR i (fderiv ℝ (V s) y (B0579.dir j))
    rw [hc, ContinuousLinearMap.comp_apply]
  have ms_coord (j i : Fin 2) :
      MemLp (fun y => (dV j y i) • ((πR j).smulRight (EuclideanSpace.single i (1 : ℝ)) (sliceR W s y)))
        2 (cellMeas c) := by
    have hcj : Continuous (fun y => dV j y i) := (πR i).continuous.comp (hcdV j)
    have hbj : ∀ y, |dV j y i| ≤ M := fun y => by rw [← hdV_eq j i y]; exact hb1 j i y
    exact memLp_mulRealR hcj hbj
      (((πR j).smulRight (EuclideanSpace.single i (1 : ℝ))).comp_memLp' hm0)
  have hm_bv : MemLp (fun y => realBvSlice (V s) (sliceR W s) (sliceR (pdR 0 W) s)
      (sliceR (pdR 1 W) s) y) 2 (cellMeas c) := by
    have heq : (fun y => realBvSlice (V s) (sliceR W s) (sliceR (pdR 0 W) s)
        (sliceR (pdR 1 W) s) y) =
        fun y => ((V s y 0 • sliceR (pdR 0 W) s y + V s y 1 • sliceR (pdR 1 W) s y) +
          (dV 0 y 0 • ((πR 0).smulRight eR0 (sliceR W s y)) +
            dV 0 y 1 • ((πR 0).smulRight eR1 (sliceR W s y)))) +
          (dV 1 y 0 • ((πR 1).smulRight eR0 (sliceR W s y)) +
            dV 1 y 1 • ((πR 1).smulRight eR1 (sliceR W s y))) := by
      funext y
      ext i
      have hd0 : ((1 : ℝ), (0 : ℝ)) = B0579.dir 0 := rfl
      have hd1 : ((0 : ℝ), (1 : ℝ)) = B0579.dir 1 := rfl
      fin_cases i <;>
        simp [realBvSlice, hd0, hd1, hdV_eq, eR0, eR1, πR] <;> ring
    rw [heq]
    exact memLp_fun_add
      (memLp_fun_add (memLp_fun_add mt0 mt1) (memLp_fun_add (ms_coord 0 0) (ms_coord 0 1)))
      (memLp_fun_add (ms_coord 1 0) (ms_coord 1 1))
  have hm_visc : MemLp (fun y => ν • (sliceR (pdR 0 (pdR 0 W)) s y +
      sliceR (pdR 1 (pdR 1 W)) s y)) 2 (cellMeas c) :=
    (memLp_fun_add hm20 hm21).const_smul ν
  exact memLp_fun_add (hms.sub hm_visc) hm_bv

lemma integrableOn_innerR_cell {c : ℝ} {f g : B0579.Plane → RMerid}
    (hf : MemLp f 2 (cellMeas c)) (hg : MemLp g 2 (cellMeas c)) :
    IntegrableOn (fun y => inner ℝ (f y) (g y)) (B0579.cell c) volume := by
  refine (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with y hyf hyg
  rw [hyf, hyg]

lemma inner_combineMerid_eq (z : CMerid) (a b : RMerid) :
    (inner ℂ z (combineMerid a b) : ℂ) =
      ((inner ℝ (reMerid z) a + inner ℝ (imMerid z) b : ℝ) : ℂ) +
        Complex.I * ((inner ℝ (reMerid z) b - inner ℝ (imMerid z) a : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [PiLp.inner_apply, Fin.sum_univ_two, combineMerid_apply]
    ring
  · simp [PiLp.inner_apply, Fin.sum_univ_two, combineMerid_apply]
    ring

lemma recombine_normalized_orbit {c ν : ℝ} {V : ℝ → B0579.Plane → RMerid}
    (hV : IsSmoothBUCDrift c V)
    {u uq uη : B0579.Plane → CMerid} (hdat : F8U.IsCylH1Datum c u uq uη)
    {W_re W_im : RProf}
    (hre : IsRealNormalizedOseenOrbit c ν V W_re
      (fun y => reMerid (u y)) (fun y => reMerid (uq y)) (fun y => reMerid (uη y)))
    (him : IsRealNormalizedOseenOrbit c ν V W_im
      (fun y => imMerid (u y)) (fun y => imMerid (uq y)) (fun y => imMerid (uη y))) :
    IsComplexNormalizedOseenOrbit c ν V
      (fun x => combineMerid (W_re x) (W_im x)) u uq uη where
  smooth := (ofRealMerid.contDiff.comp_contDiffOn hre.smooth).add
    (ofImagMerid.contDiff.comp_contDiffOn him.smooth)
  periodic x hx := by
    dsimp only [combineMerid]
    rw [hre.periodic x hx, him.periodic x hx]
  div_free x hx := by
    have h0 := pdIter_combineMerid hre.smooth him.smooth ![0] ⟨hx, trivial⟩
    have h1 := pdIter_combineMerid hre.smooth him.smooth ![1] ⟨hx, trivial⟩
    change F8U.pd 0 (fun z => combineMerid (W_re z) (W_im z)) x =
      combineMerid (pdR 0 W_re x) (pdR 0 W_im x) at h0
    change F8U.pd 1 (fun z => combineMerid (W_re z) (W_im z)) x =
      combineMerid (pdR 1 W_re x) (pdR 1 W_im x) at h1
    rw [h0, h1, combineMerid_apply, combineMerid_apply]
    have hd_re := hre.div_free x hx
    have hd_im := him.div_free x hx
    calc ((pdR 0 W_re x 0 : ℂ) + Complex.I * (pdR 0 W_im x 0 : ℂ)) +
          ((pdR 1 W_re x 1 : ℂ) + Complex.I * (pdR 1 W_im x 1 : ℂ))
        = ((pdR 0 W_re x 0 + pdR 1 W_re x 1 : ℝ) : ℂ) +
            Complex.I * ((pdR 0 W_im x 0 + pdR 1 W_im x 1 : ℝ) : ℂ) := by push_cast; ring
      _ = 0 := by rw [hd_re, hd_im]; simp
  memL2 s hs n hn α := by
    have heq : F8U.slice (F8U.pdIter α (fun z => combineMerid (W_re z) (W_im z))) s =
        fun y => combineMerid (sliceR (pdIterR α W_re) s y) (sliceR (pdIterR α W_im) s y) := by
      funext y
      exact pdIter_combineMerid hre.smooth him.smooth α ⟨hs, trivial⟩
    rw [heq]
    exact memLp_fun_add
      (ofRealMerid.comp_memLp' (hre.memL2 s hs n hn α))
      (ofImagMerid.comp_memLp' (him.memL2 s hs n hn α))
  memL2_s s hs n hn α := by
    have heq : F8U.slice (F8U.ps (F8U.pdIter α (fun z => combineMerid (W_re z) (W_im z)))) s =
        fun y => combineMerid (sliceR (psR (pdIterR α W_re)) s y)
          (sliceR (psR (pdIterR α W_im)) s y) := by
      funext y
      exact ps_pdIter_combineMerid hre.smooth him.smooth α ⟨hs, trivial⟩
    rw [heq]
    exact memLp_fun_add
      (ofRealMerid.comp_memLp' (hre.memL2_s s hs n hn α))
      (ofImagMerid.comp_memLp' (him.memL2_s s hs n hn α))
  cont s hs n hn α := by
    have hsum := (hre.cont s hs n hn α).add (him.cont s hs n hn α)
    rw [add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
    have heq : (fun y => F8U.pdIter α (fun z => combineMerid (W_re z) (W_im z)) (t, y) -
        F8U.pdIter α (fun z => combineMerid (W_re z) (W_im z)) (s, y)) =
        fun y => combineMerid (pdIterR α W_re (t, y) - pdIterR α W_re (s, y))
          (pdIterR α W_im (t, y) - pdIterR α W_im (s, y)) := by
      funext y
      rw [pdIter_combineMerid hre.smooth him.smooth α ⟨ht, trivial⟩,
        pdIter_combineMerid hre.smooth him.smooth α ⟨hs, trivial⟩]
      unfold combineMerid
      rw [map_sub, map_sub, add_sub_add_comm]
    rw [heq]
    exact cellL2_combineMerid_le
      ((hre.memL2 t ht n hn α).sub (hre.memL2 s hs n hn α))
      ((him.memL2 t ht n hn α).sub (him.memL2 s hs n hn α))
  cont_s s hs n hn α := by
    have hsum := (hre.cont_s s hs n hn α).add (him.cont_s s hs n hn α)
    rw [add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
    have heq : (fun y => F8U.ps (F8U.pdIter α (fun z => combineMerid (W_re z) (W_im z))) (t, y) -
        F8U.ps (F8U.pdIter α (fun z => combineMerid (W_re z) (W_im z))) (s, y)) =
        fun y => combineMerid (psR (pdIterR α W_re) (t, y) - psR (pdIterR α W_re) (s, y))
          (psR (pdIterR α W_im) (t, y) - psR (pdIterR α W_im) (s, y)) := by
      funext y
      rw [ps_pdIter_combineMerid hre.smooth him.smooth α ⟨ht, trivial⟩,
        ps_pdIter_combineMerid hre.smooth him.smooth α ⟨hs, trivial⟩]
      unfold combineMerid
      rw [map_sub, map_sub, add_sub_add_comm]
    rw [heq]
    exact cellL2_combineMerid_le
      ((hre.memL2_s t ht n hn α).sub (hre.memL2_s s hs n hn α))
      ((him.memL2_s t ht n hn α).sub (him.memL2_s s hs n hn α))
  projected s hs φ hmφ hsolφ := by
    obtain ⟨hsol_re, hsol_im⟩ := isRealCellSolenoidal_re_im hsolφ
    have hmφ_re : MemLp (fun y => reMerid (φ y)) 2 (cellMeas c) := reMerid.comp_memLp' hmφ
    have hmφ_im : MemLp (fun y => imMerid (φ y)) 2 (cellMeas c) := imMerid.comp_memLp' hmφ
    have hmR_re : MemLp (fun y => realHomResidual ν V W_re (s, y)) 2 (cellMeas c) :=
      memLp_realHomResidual hV hre hs
    have hmR_im : MemLp (fun y => realHomResidual ν V W_im (s, y)) 2 (cellMeas c) :=
      memLp_realHomResidual hV him hs
    have hi_rr := integrableOn_innerR_cell hmφ_re hmR_re
    have hi_ii := integrableOn_innerR_cell hmφ_im hmR_im
    have hi_ri := integrableOn_innerR_cell hmφ_re hmR_im
    have hi_ir := integrableOn_innerR_cell hmφ_im hmR_re
    have h0_rr := hre.projected s hs _ hmφ_re hsol_re
    have h0_ii := him.projected s hs _ hmφ_im hsol_im
    have h0_ri := him.projected s hs _ hmφ_re hsol_re
    have h0_ir := hre.projected s hs _ hmφ_im hsol_im
    have hexp : (fun y => (inner ℂ (φ y)
        (normHomResidual ν V (fun z => combineMerid (W_re z) (W_im z)) (s, y)) : ℂ)) =
        fun y => (((inner ℝ (reMerid (φ y)) (realHomResidual ν V W_re (s, y)) +
            inner ℝ (imMerid (φ y)) (realHomResidual ν V W_im (s, y)) : ℝ) : ℂ) +
          Complex.I * ((inner ℝ (reMerid (φ y)) (realHomResidual ν V W_im (s, y)) -
            inner ℝ (imMerid (φ y)) (realHomResidual ν V W_re (s, y)) : ℝ) : ℂ)) := by
      funext y
      rw [normHomResidual_combineMerid hre.smooth him.smooth hs y, inner_combineMerid_eq]
    have hi_c1 : IntegrableOn
        (fun y => ((inner ℝ (reMerid (φ y)) (realHomResidual ν V W_re (s, y)) +
          inner ℝ (imMerid (φ y)) (realHomResidual ν V W_im (s, y)) : ℝ) : ℂ))
        (B0579.cell c) volume :=
      Complex.ofRealCLM.integrable_comp (hi_rr.add hi_ii)
    have hi_c2 : IntegrableOn
        (fun y => Complex.I * ((inner ℝ (reMerid (φ y)) (realHomResidual ν V W_im (s, y)) -
          inner ℝ (imMerid (φ y)) (realHomResidual ν V W_re (s, y)) : ℝ) : ℂ))
        (B0579.cell c) volume :=
      (Complex.ofRealCLM.integrable_comp (hi_ri.sub hi_ir)).const_mul Complex.I
    rw [hexp, integral_add hi_c1 hi_c2, integral_const_mul]
    have hc1 := Complex.ofRealCLM.integral_comp_comm (hi_rr.add hi_ii)
    have hc2 := Complex.ofRealCLM.integral_comp_comm (hi_ri.sub hi_ir)
    simp only [Complex.ofRealCLM_apply, Pi.add_apply, Pi.sub_apply] at hc1 hc2
    rw [hc1, hc2, integral_add hi_rr hi_ii, integral_sub hi_ri hi_ir,
      h0_rr, h0_ii, h0_ri, h0_ir]
    simp
  initial := by
    have hsum := hre.initial.add him.initial
    rw [add_zero] at hsum
    have hev_Ioo : Ioo (0 : ℝ) 2 ∈ 𝓝[>] (0 : ℝ) :=
      Filter.inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num)))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [hev_Ioo] with t ht
    have h0_eq : (fun y => combineMerid (W_re (t, y)) (W_im (t, y)) - u y) =
        fun y => combineMerid (W_re (t, y) - reMerid (u y)) (W_im (t, y) - imMerid (u y)) := by
      funext y
      conv_lhs => rw [← combineMerid_re_im (u y)]
      unfold combineMerid
      rw [map_sub, map_sub, add_sub_add_comm]
    have hq_eq : (fun y => F8U.pd 0 (fun z => combineMerid (W_re z) (W_im z)) (t, y) - uq y) =
        fun y => combineMerid (pdR 0 W_re (t, y) - reMerid (uq y))
          (pdR 0 W_im (t, y) - imMerid (uq y)) := by
      funext y
      have hp := pdIter_combineMerid hre.smooth him.smooth ![0] (x := (t, y)) ⟨ht, trivial⟩
      change F8U.pd 0 (fun z => combineMerid (W_re z) (W_im z)) (t, y) =
        combineMerid (pdR 0 W_re (t, y)) (pdR 0 W_im (t, y)) at hp
      rw [hp]
      conv_lhs => rw [← combineMerid_re_im (uq y)]
      unfold combineMerid
      rw [map_sub, map_sub, add_sub_add_comm]
    have he_eq : (fun y => F8U.pd 1 (fun z => combineMerid (W_re z) (W_im z)) (t, y) - uη y) =
        fun y => combineMerid (pdR 1 W_re (t, y) - reMerid (uη y))
          (pdR 1 W_im (t, y) - imMerid (uη y)) := by
      funext y
      have hp := pdIter_combineMerid hre.smooth him.smooth ![1] (x := (t, y)) ⟨ht, trivial⟩
      change F8U.pd 1 (fun z => combineMerid (W_re z) (W_im z)) (t, y) =
        combineMerid (pdR 1 W_re (t, y)) (pdR 1 W_im (t, y)) at hp
      rw [hp]
      conv_lhs => rw [← combineMerid_re_im (uη y)]
      unfold combineMerid
      rw [map_sub, map_sub, add_sub_add_comm]
    have hb0 : F8U.cellL2 c (fun y => combineMerid (W_re (t, y)) (W_im (t, y)) - u y) ≤
        cellL2R c (fun y => W_re (t, y) - reMerid (u y)) +
          cellL2R c (fun y => W_im (t, y) - imMerid (u y)) := by
      rw [h0_eq]
      exact cellL2_combineMerid_le
        ((hre.memL2 t ht 0 (by decide) ![]).sub (reMerid.comp_memLp' hdat.memL2.1))
        ((him.memL2 t ht 0 (by decide) ![]).sub (imMerid.comp_memLp' hdat.memL2.1))
    have hbq : F8U.cellL2 c
        (fun y => F8U.pd 0 (fun z => combineMerid (W_re z) (W_im z)) (t, y) - uq y) ≤
        cellL2R c (fun y => pdR 0 W_re (t, y) - reMerid (uq y)) +
          cellL2R c (fun y => pdR 0 W_im (t, y) - imMerid (uq y)) := by
      rw [hq_eq]
      exact cellL2_combineMerid_le
        ((hre.memL2 t ht 1 (by decide) ![0]).sub (reMerid.comp_memLp' hdat.memL2.2.1))
        ((him.memL2 t ht 1 (by decide) ![0]).sub (imMerid.comp_memLp' hdat.memL2.2.1))
    have hbe : F8U.cellL2 c
        (fun y => F8U.pd 1 (fun z => combineMerid (W_re z) (W_im z)) (t, y) - uη y) ≤
        cellL2R c (fun y => pdR 1 W_re (t, y) - reMerid (uη y)) +
          cellL2R c (fun y => pdR 1 W_im (t, y) - imMerid (uη y)) := by
      rw [he_eq]
      exact cellL2_combineMerid_le
        ((hre.memL2 t ht 1 (by decide) ![1]).sub (reMerid.comp_memLp' hdat.memL2.2.2))
        ((him.memL2 t ht 1 (by decide) ![1]).sub (imMerid.comp_memLp' hdat.memL2.2.2))
    calc F8U.cylH1 c (fun y => combineMerid (W_re (t, y)) (W_im (t, y)) - u y)
          (fun y => F8U.pd 0 (fun z => combineMerid (W_re z) (W_im z)) (t, y) - uq y)
          (fun y => F8U.pd 1 (fun z => combineMerid (W_re z) (W_im z)) (t, y) - uη y)
        ≤ (cellL2R c (fun y => W_re (t, y) - reMerid (u y)) +
            cellL2R c (fun y => W_im (t, y) - imMerid (u y))) +
          (cellL2R c (fun y => pdR 0 W_re (t, y) - reMerid (uq y)) +
            cellL2R c (fun y => pdR 0 W_im (t, y) - imMerid (uq y))) +
          (cellL2R c (fun y => pdR 1 W_re (t, y) - reMerid (uη y)) +
            cellL2R c (fun y => pdR 1 W_im (t, y) - imMerid (uη y))) :=
          add_le_add (add_le_add hb0 hbq) hbe
      _ = cylH1R c (fun y => W_re (t, y) - reMerid (u y))
            (fun y => pdR 0 W_re (t, y) - reMerid (uq y))
            (fun y => pdR 1 W_re (t, y) - reMerid (uη y)) +
          cylH1R c (fun y => W_im (t, y) - imMerid (u y))
            (fun y => pdR 0 W_im (t, y) - imMerid (uq y))
            (fun y => pdR 1 W_im (t, y) - imMerid (uη y)) := by
          unfold cylH1R
          ac_rfl

/-! ## 5. Age-shift equivalence `(0, 2) ↔ (σ, σ + 2)` -/

/-- Age translation `(τ, y) ↦ (τ - σ, y)` on `Coord = ℝ × (ℝ × ℝ)`. -/
def shiftSub (σ : ℝ) (x : Coord) : Coord := (x.1 - σ, x.2)

lemma shiftSub_eq_add (σ : ℝ) (z : Coord) : shiftSub σ z = z + (-σ, (0, 0)) := by
  ext <;> simp [shiftSub, sub_eq_add_neg]

lemma contDiff_shiftSub (σ : ℝ) : ContDiff ℝ ∞ (shiftSub σ) :=
  (contDiff_fst.sub contDiff_const).prodMk contDiff_snd

lemma fderiv_comp_shiftSub (σ : ℝ) (G : CProf) (x : Coord) :
    fderiv ℝ (fun z => G (shiftSub σ z)) x = fderiv ℝ G (shiftSub σ x) := by
  simp only [shiftSub_eq_add σ]
  exact fderiv_comp_add_right (𝕜 := ℝ) (f := G) (x := x) ((-σ, (0, 0)) : Coord)

lemma pd_comp_shiftSub (σ : ℝ) (i : Fin 2) (G : CProf) :
    F8U.pd i (fun z => G (shiftSub σ z)) = fun z => F8U.pd i G (shiftSub σ z) := by
  funext x
  unfold F8U.pd
  rw [fderiv_comp_shiftSub]

lemma ps_comp_shiftSub (σ : ℝ) (G : CProf) :
    F8U.ps (fun z => G (shiftSub σ z)) = fun z => F8U.ps G (shiftSub σ z) := by
  funext x
  unfold F8U.ps
  rw [fderiv_comp_shiftSub]

lemma pdIter_comp_shiftSub (σ : ℝ) :
    ∀ {n : ℕ} (α : Fin n → Fin 2) (W : CProf),
      F8U.pdIter α (fun z => W (shiftSub σ z)) = fun z => F8U.pdIter α W (shiftSub σ z)
  | 0, _, _ => rfl
  | _ + 1, α, W => by
      simp only [F8U.pdIter, pdIter_comp_shiftSub σ (Fin.tail α) W, pd_comp_shiftSub]

lemma homResidual_comp_shiftSub (p : Params) (σ : ℝ) (W : CProf) (τ : ℝ) (y : B0579.Plane) :
    F8U.homResidual p (fun z => W (shiftSub σ z)) (τ, y) =
      normHomResidual p.ν (shiftedDrift p σ) W (τ - σ, y) := by
  have hτ : σ + (τ - σ) = τ := add_sub_cancel σ τ
  unfold F8U.homResidual normHomResidual
  simp only [ps_comp_shiftSub, pd_comp_shiftSub]
  dsimp only [shiftSub, F8U.slice]
  congr 1
  ext i
  simp only [flatBv, complexBvSlice, shiftedDrift, shiftedDriftTrain, F8U.slice, hτ]

lemma shift_orbit_from_zero {p : Params} {σ : ℝ} {u uq uη : B0579.Plane → CMerid} {W : CProf}
    (hW : IsComplexNormalizedOseenOrbit p.c p.ν (shiftedDrift p σ) W u uq uη) :
    F8U.IsCylOseenOrbit p σ (fun z => W (shiftSub σ z)) u uq uη := by
  constructor
  · exact hW.smooth.comp (contDiff_shiftSub σ).contDiffOn
      (fun x hx => ⟨⟨by dsimp [shiftSub]; linarith [hx.1.1],
        by dsimp [shiftSub]; linarith [hx.1.2]⟩, mem_univ _⟩)
  · intro x hx
    have hq : shiftSub σ (qShift p.c x) = qShift p.c (shiftSub σ x) := rfl
    rw [hq]
    exact hW.periodic (shiftSub σ x) ⟨by dsimp [shiftSub]; linarith [hx.1],
      by dsimp [shiftSub]; linarith [hx.2]⟩
  · intro x hx
    simp only [pd_comp_shiftSub]
    exact hW.div_free (shiftSub σ x) ⟨by dsimp [shiftSub]; linarith [hx.1],
      by dsimp [shiftSub]; linarith [hx.2]⟩
  · intro τ hτ n hn α
    have hs : τ - σ ∈ Ioo (0 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have hf : F8U.slice (fun z => F8U.pdIter α W (shiftSub σ z)) τ =
        F8U.slice (F8U.pdIter α W) (τ - σ) := rfl
    rw [pdIter_comp_shiftSub, hf]
    exact hW.memL2 (τ - σ) hs n hn α
  · intro τ hτ n hn α
    have hs : τ - σ ∈ Ioo (0 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have hf : F8U.slice (fun z => F8U.ps (F8U.pdIter α W) (shiftSub σ z)) τ =
        F8U.slice (F8U.ps (F8U.pdIter α W)) (τ - σ) := rfl
    rw [pdIter_comp_shiftSub, ps_comp_shiftSub, hf]
    exact hW.memL2_s (τ - σ) hs n hn α
  · intro τ hτ n hn α
    have hs : τ - σ ∈ Ioo (0 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have hsub : Tendsto (fun t : ℝ => t - σ) (𝓝 τ) (𝓝 (τ - σ)) :=
      (continuous_sub_right σ).tendsto τ
    simp only [pdIter_comp_shiftSub]
    simpa only [Function.comp_def, shiftSub] using (hW.cont (τ - σ) hs n hn α).comp hsub
  · intro τ hτ n hn α
    have hs : τ - σ ∈ Ioo (0 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have hsub : Tendsto (fun t : ℝ => t - σ) (𝓝 τ) (𝓝 (τ - σ)) :=
      (continuous_sub_right σ).tendsto τ
    simp only [pdIter_comp_shiftSub, ps_comp_shiftSub]
    simpa only [Function.comp_def, shiftSub] using (hW.cont_s (τ - σ) hs n hn α).comp hsub
  · intro τ hτ φ hmφ hsolφ
    have hs : τ - σ ∈ Ioo (0 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    simp_rw [homResidual_comp_shiftSub p σ W τ]
    exact hW.projected (τ - σ) hs φ hmφ hsolφ
  · have hsub0 : Tendsto (fun t : ℝ => t - σ) (𝓝[>] σ) (𝓝 0) := by
      simpa only [sub_self] using
        ((continuous_sub_right σ).tendsto σ).mono_left nhdsWithin_le_nhds
    have hsub_gt : Tendsto (fun t : ℝ => t - σ) (𝓝[>] σ) (𝓝[>] (0 : ℝ)) :=
      tendsto_nhdsWithin_iff.2
        ⟨hsub0, Filter.Eventually.mono self_mem_nhdsWithin fun t (ht : σ < t) => sub_pos.mpr ht⟩
    simp only [pd_comp_shiftSub]
    simpa only [Function.comp_def, shiftSub] using hW.initial.comp hsub_gt

/-! ## 5b. Slice-level `C((0, 2); H^∞(C_c))` smooth slices and joint-smoothness bridge -/

/-- Slice-level spatial partial derivative `∂_q f` (`i = 0`) or `∂_η f` (`i = 1`) on `ℝ²`
(independent of age differentiability). -/
def slicePdR (i : Fin 2) (f : B0579.Plane → RMerid) (y : B0579.Plane) : RMerid :=
  fderiv ℝ f y (B0579.dir i)

/-- Iterated slice-level spatial derivative `∂^α f` on `ℝ²` for `α : Fin n → Fin 2`. -/
def slicePdIterR : {n : ℕ} → (Fin n → Fin 2) → (B0579.Plane → RMerid) → B0579.Plane → RMerid
  | 0, _, f => f
  | n + 1, α, f => slicePdR (α 0) (slicePdIterR (n := n) (Fin.tail α) f)

/-- Spatially `C^∞`, `c`-periodic, divergence-free `C((0, 2); H^∞(C_c))` representative `w` on
`(0, 2)` of a weak `H¹_σ(C_c)` Oseen solution `(W, Wq, Wη)` (purely spatial slice regularity on
each `s ∈ (0, 2)`, prior to upgrading to joint space-time `C^∞` regularity). -/
structure IsRealSpatialSmoothOseenSlices (c : ℝ)
    (w : ℝ → B0579.Plane → RMerid) (W Wq Wη : ℝ → B0579.Plane → RMerid) : Prop where
  ae_val : ∀ s ∈ Ioo (0 : ℝ) 2, w s =ᵐ[cellMeas c] W s
  ae_dq : ∀ s ∈ Ioo (0 : ℝ) 2, slicePdR 0 (w s) =ᵐ[cellMeas c] Wq s
  ae_deta : ∀ s ∈ Ioo (0 : ℝ) 2, slicePdR 1 (w s) =ᵐ[cellMeas c] Wη s
  spatial_smooth : ∀ s ∈ Ioo (0 : ℝ) 2, ContDiff ℝ ∞ (w s)
  periodic : ∀ s ∈ Ioo (0 : ℝ) 2, ∀ y : B0579.Plane, w s (y.1 + c, y.2) = w s y
  div_free : ∀ s ∈ Ioo (0 : ℝ) 2, ∀ y : B0579.Plane,
    slicePdR 0 (w s) y 0 + slicePdR 1 (w s) y 1 = 0
  memL2_all : ∀ s ∈ Ioo (0 : ℝ) 2, ∀ (n : ℕ) (α : Fin n → Fin 2),
    MemLp (slicePdIterR α (w s)) 2 (cellMeas c)
  cont_all : ∀ s ∈ Ioo (0 : ℝ) 2, ∀ (n : ℕ) (α : Fin n → Fin 2),
    Tendsto (fun t => cellL2R c (fun y => slicePdIterR α (w t) y - slicePdIterR α (w s) y))
      (𝓝 s) (𝓝 0)

lemma sdir_eq_zero_dir (i : Fin 2) : F8U.sdir i = ((0 : ℝ), B0579.dir i) := by
  fin_cases i <;> rfl

lemma pdR_uncurry_eq_slicePdR {W : RProf} (hsm : ContDiffOn ℝ ∞ W strip0)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 2) (i : Fin 2) (y : B0579.Plane) :
    pdR i W (s, y) = slicePdR i (sliceR W s) y := by
  have hx : (s, y) ∈ strip0 := ⟨hs, trivial⟩
  have hdW : DifferentiableAt ℝ W (s, y) :=
    (hsm.contDiffAt (isOpen_strip0.mem_nhds hx)).differentiableAt (by simp)
  have hemb : HasFDerivAt (fun z : B0579.Plane => (s, z))
      ((0 : B0579.Plane →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ B0579.Plane)) y :=
    (hasFDerivAt_const s y).prodMk (hasFDerivAt_id y)
  have hcomp : HasFDerivAt (sliceR W s)
      ((fderiv ℝ W (s, y)).comp
        ((0 : B0579.Plane →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ B0579.Plane))) y :=
    hdW.hasFDerivAt.comp y hemb
  unfold pdR slicePdR
  rw [hcomp.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply, ContinuousLinearMap.id_apply, sdir_eq_zero_dir]

lemma pdIterR_uncurry_eq_slicePdIterR {W : RProf} (hsm : ContDiffOn ℝ ∞ W strip0) :
    ∀ {n : ℕ} (α : Fin n → Fin 2) {s : ℝ}, s ∈ Ioo (0 : ℝ) 2 → ∀ y : B0579.Plane,
      pdIterR α W (s, y) = slicePdIterR α (sliceR W s) y
  | 0, _, _, _, _ => rfl
  | _ + 1, α, s, hs, y => by
      have htail_sm : ContDiffOn ℝ ∞ (pdIterR (Fin.tail α) W) strip0 :=
        contDiffOn_pdR hsm (Fin.tail α)
      have hfun : sliceR (pdIterR (Fin.tail α) W) s = slicePdIterR (Fin.tail α) (sliceR W s) := by
        funext z
        exact pdIterR_uncurry_eq_slicePdIterR hsm (Fin.tail α) hs z
      simp only [pdIterR, slicePdIterR]
      rw [pdR_uncurry_eq_slicePdR htail_sm hs (α 0) y, hfun]

/-- Chain-rule assembly reducing `IsRealInteriorSmoothOrbit` for `W_reg (x) := w x.1 x.2` (given
`IsRealSpatialSmoothOseenSlices c w W Wq Wη`) to joint `C^∞` regularity, `(1, ≤2)` slice `L²`
bounds/continuity, and `L²_σ` orthogonality of `realHomResidual`. -/
lemma isRealInteriorSmoothOrbit_of_joint {c ν : ℝ} {V : ℝ → B0579.Plane → RMerid}
    {w W Wq Wη : ℝ → B0579.Plane → RMerid}
    (hsp : IsRealSpatialSmoothOseenSlices c w W Wq Wη)
    (hsmooth : ContDiffOn ℝ ∞ (fun x : Coord => w x.1 x.2) (Ioo (0 : ℝ) 2 ×ˢ univ))
    (hmem_s : ∀ s ∈ Ioo (0 : ℝ) 2, ∀ n : ℕ, n ≤ 2 → ∀ α : Fin n → Fin 2,
      MemLp (sliceR (psR (pdIterR α (fun x : Coord => w x.1 x.2))) s) 2 (cellMeas c))
    (hcont_s : ∀ s ∈ Ioo (0 : ℝ) 2, ∀ n : ℕ, n ≤ 2 → ∀ α : Fin n → Fin 2,
      Tendsto (fun t => cellL2R c (fun y =>
        psR (pdIterR α (fun x : Coord => w x.1 x.2)) (t, y) -
          psR (pdIterR α (fun x : Coord => w x.1 x.2)) (s, y))) (𝓝 s) (𝓝 0))
    (hproj : ∀ s ∈ Ioo (0 : ℝ) 2, ∀ φ : B0579.Plane → RMerid,
      MemLp φ 2 (cellMeas c) → IsRealCellSolenoidal c φ →
        ∫ y in B0579.cell c,
          inner ℝ (φ y) (realHomResidual ν V (fun x : Coord => w x.1 x.2) (s, y)) = 0) :
    IsRealInteriorSmoothOrbit c ν V (fun x : Coord => w x.1 x.2) W Wq Wη where
  ae_val s hs := hsp.ae_val s hs
  ae_dq s hs := by
    have h0 : sliceR (pdR 0 (fun x : Coord => w x.1 x.2)) s = slicePdR 0 (w s) := by
      funext y
      exact pdR_uncurry_eq_slicePdR hsmooth hs 0 y
    rw [h0]
    exact hsp.ae_dq s hs
  ae_deta s hs := by
    have h1 : sliceR (pdR 1 (fun x : Coord => w x.1 x.2)) s = slicePdR 1 (w s) := by
      funext y
      exact pdR_uncurry_eq_slicePdR hsmooth hs 1 y
    rw [h1]
    exact hsp.ae_deta s hs
  smooth := hsmooth
  periodic x hx := hsp.periodic x.1 hx x.2
  div_free x hx := by
    rw [pdR_uncurry_eq_slicePdR hsmooth hx 0 x.2, pdR_uncurry_eq_slicePdR hsmooth hx 1 x.2]
    exact hsp.div_free x.1 hx x.2
  memL2 s hs n _ α := by
    have hα : sliceR (pdIterR α (fun x : Coord => w x.1 x.2)) s = slicePdIterR α (w s) := by
      funext y
      exact pdIterR_uncurry_eq_slicePdIterR hsmooth α hs y
    rw [hα]
    exact hsp.memL2_all s hs n α
  memL2_s := hmem_s
  cont s hs n _ α := by
    refine (hsp.cont_all s hs n α).congr' ?_
    filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
    have hα : (fun y => pdIterR α (fun x : Coord => w x.1 x.2) (t, y) -
        pdIterR α (fun x : Coord => w x.1 x.2) (s, y)) =
        fun y => slicePdIterR α (w t) y - slicePdIterR α (w s) y := by
      funext y
      rw [pdIterR_uncurry_eq_slicePdIterR hsmooth α ht y,
        pdIterR_uncurry_eq_slicePdIterR hsmooth α hs y]
      rfl
    rw [hα]
  cont_s := hcont_s
  projected := hproj

lemma memLp_realSolCylTest {c : ℝ} {Φ : B0579.Plane → RMerid} (hΦ : IsRealSolCylTest c Φ) :
    MemLp Φ 2 (cellMeas c) := by
  obtain ⟨R0, hR0⟩ := (hΦ.cyl_test 0).vanish
  obtain ⟨R1, hR1⟩ := (hΦ.cyl_test 1).vanish
  have hm0 : MemLp (fun y => Φ y 0) 2 (cellMeas c) :=
    B0579.memLp_cell_of_continuous (hΦ.cyl_test 0).continuous (B0579.isCompact_box c R0) hR0
  have hm1 : MemLp (fun y => Φ y 1) 2 (cellMeas c) :=
    B0579.memLp_cell_of_continuous (hΦ.cyl_test 1).continuous (B0579.isCompact_box c R1) hR1
  have heq : Φ = fun y => (ContinuousLinearMap.id ℝ ℝ).smulRight eR0 (Φ y 0) +
      (ContinuousLinearMap.id ℝ ℝ).smulRight eR1 (Φ y 1) := by
    funext y
    ext k
    fin_cases k <;> simp [eR0, eR1]
  rw [heq]
  exact memLp_fun_add
    (((ContinuousLinearMap.id ℝ ℝ).smulRight eR0).comp_memLp' hm0)
    (((ContinuousLinearMap.id ℝ ℝ).smulRight eR1).comp_memLp' hm1)

/-- Subinterval weak identity on `(0, 2)` transferred to spatially smooth slices `w`. -/
lemma weak_eq_sub_of_slices {c ν : ℝ} {V : ℝ → B0579.Plane → RMerid}
    {u uq uη : B0579.Plane → RMerid} {W Wq Wη w : ℝ → B0579.Plane → RMerid}
    (hdat : IsRealCylH1Datum c u uq uη)
    (hwk : IsRealWeakH1OseenSol c ν V W Wq Wη u uq uη)
    (hsp : IsRealSpatialSmoothOseenSlices c w W Wq Wη)
    {a t : ℝ} (ha : a ∈ Ioo (0 : ℝ) 2) (ht : t ∈ Ioo (0 : ℝ) 2)
    {Φ : B0579.Plane → RMerid} (hΦ : IsRealSolCylTest c Φ) :
    let F_sp : ℝ → ℝ := fun r => ∫ y in B0579.cell c,
      (ν * (∑ k : Fin 2, (B0579.pd 0 (fun z => Φ z k) y * slicePdR 0 (w r) y k +
          B0579.pd 1 (fun z => Φ z k) y * slicePdR 1 (w r) y k)) +
        inner ℝ (Φ y) (realBvSlice (V r) (w r) (slicePdR 0 (w r)) (slicePdR 1 (w r)) y))
    IntervalIntegrable F_sp volume a t ∧
      (∫ y in B0579.cell c, inner ℝ (Φ y) (w t y - w a y)) + ∫ r in a..t, F_sp r = 0 := by
  intro F_sp
  let F_wk : ℝ → ℝ := fun r => ∫ y in B0579.cell c,
    (ν * (∑ k : Fin 2, (B0579.pd 0 (fun z => Φ z k) y * Wq r y k +
        B0579.pd 1 (fun z => Φ z k) y * Wη r y k)) +
      inner ℝ (Φ y) (realBvSlice (V r) (W r) (Wq r) (Wη r) y))
  have hF_eq : ∀ r ∈ Ioo (0 : ℝ) 2, F_sp r = F_wk r := by
    intro r hr
    dsimp only [F_sp, F_wk]
    refine integral_congr_ae ?_
    filter_upwards [hsp.ae_val r hr, hsp.ae_dq r hr, hsp.ae_deta r hr] with y h0 hq he
    simp only [realBvSlice, h0, hq, he]
  have huIcc_sub : uIcc a t ⊆ Ioo (0 : ℝ) 2 := fun r hr =>
    ⟨lt_of_lt_of_le (lt_min ha.1 ht.1) hr.1, lt_of_le_of_lt hr.2 (max_lt ha.2 ht.2)⟩
  have huIoc_eq : EqOn F_sp F_wk (uIoc a t) :=
    fun r hr => hF_eq r (huIcc_sub (uIoc_subset_uIcc hr))
  obtain ⟨hi_02, _⟩ := hwk.weak_eq Φ hΦ 2 ⟨by norm_num, le_rfl⟩
  obtain ⟨hi_0a, heq_a⟩ := hwk.weak_eq Φ hΦ a ⟨ha.1.le, ha.2.le⟩
  obtain ⟨hi_0t, heq_t⟩ := hwk.weak_eq Φ hΦ t ⟨ht.1.le, ht.2.le⟩
  have hi_wk_at : IntervalIntegrable F_wk volume a t :=
    hi_02.mono_set (by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
      exact fun r hr => ⟨(huIcc_sub hr).1.le, (huIcc_sub hr).2.le⟩)
  have hi_sp_at : IntervalIntegrable F_sp volume a t :=
    hi_wk_at.congr huIoc_eq.symm
  have hadj : (∫ r in (0 : ℝ)..a, F_wk r) + (∫ r in a..t, F_wk r) = ∫ r in (0 : ℝ)..t, F_wk r :=
    intervalIntegral.integral_add_adjacent_intervals hi_0a hi_wk_at
  have hint_eq : ∫ r in a..t, F_sp r = ∫ r in a..t, F_wk r :=
    intervalIntegral.integral_congr fun r hr => hF_eq r (huIcc_sub hr)
  have hmΦ : MemLp Φ 2 (cellMeas c) := memLp_realSolCylTest hΦ
  have hmWt : MemLp (W t) 2 (cellMeas c) := (hwk.slice_h1 t ⟨ht.1.le, ht.2.le⟩).memL2.1
  have hmWa : MemLp (W a) 2 (cellMeas c) := (hwk.slice_h1 a ⟨ha.1.le, ha.2.le⟩).memL2.1
  have hi_tu : IntegrableOn (fun y => inner ℝ (Φ y) (W t y - u y)) (B0579.cell c) volume :=
    integrableOn_innerR_cell hmΦ (hmWt.sub hdat.memL2.1)
  have hi_au : IntegrableOn (fun y => inner ℝ (Φ y) (W a y - u y)) (B0579.cell c) volume :=
    integrableOn_innerR_cell hmΦ (hmWa.sub hdat.memL2.1)
  have hdiff_cell : ∫ y in B0579.cell c, inner ℝ (Φ y) (w t y - w a y) =
      (∫ y in B0579.cell c, inner ℝ (Φ y) (W t y - u y)) -
        (∫ y in B0579.cell c, inner ℝ (Φ y) (W a y - u y)) := by
    rw [← integral_sub hi_tu hi_au]
    refine integral_congr_ae ?_
    filter_upwards [hsp.ae_val t ht, hsp.ae_val a ha] with y hyt hya
    rw [hyt, hya, ← inner_sub_right]
    congr 1
    abel
  refine ⟨hi_sp_at, ?_⟩
  rw [hdiff_cell, hint_eq]
  linarith [heq_a, heq_t, hadj]

end F8Ex

/-! ## 6. Self-contained real `[0, 2]` PDE leaves and conditional assembly of `CylOseenOrbitExists` -/

/-- **Leaf 1 for `PartII-b:F8/1/org/2` (`RealCylOseenWeakH1Exists`, task `PartII-b:F8/1/org/2/1`,
SP 2213–2217, 2296–2297)**: Galerkin or mild `e^{ντΔ} P_0` semigroup existence in
`C([0, 2]; H¹_σ(C_c))` for the real periodic-cylinder Oseen equation
`∂_s W - ν Δ W + P_0(V(s)·∇W + W·∇V(s)) = 0` on `[0, 2]` with `c > 0`, `ν > 0`, smooth `c`-periodic
divergence-free drift `V` having uniformly bounded spatial derivatives on `[0, 2] × ℝ²`
(`F8Ex.IsSmoothBUCDrift c V`), and arbitrary real solenoidal initial datum `(u, uq, uη)` in
`H¹_σ(C_c)` (`F8Ex.IsRealCylH1Datum c u uq uη`). Composed in `PartII-b:F8/1/org/2`. -/
def RealCylOseenWeakH1Exists : Prop :=
  ∀ (c ν : ℝ), 0 < c → 0 < ν →
    ∀ V : ℝ → B0579.Plane → F8Ex.RMerid, F8Ex.IsSmoothBUCDrift c V →
      ∀ u uq uη : B0579.Plane → F8Ex.RMerid, F8Ex.IsRealCylH1Datum c u uq uη →
        ∃ W Wq Wη : ℝ → B0579.Plane → F8Ex.RMerid,
          F8Ex.IsRealWeakH1OseenSol c ν V W Wq Wη u uq uη

/-- **Leaf 2 for `PartII-b:F8/1/org/2` (`RealCylOseenSpatialBootstrap`, task
`PartII-b:F8/1/org/2/2`, SP 2052–2053, 2213–2217, 2296–2301)**: interior spatial parabolic
bootstrap on `(0, 2)` for a weak `C([0, 2]; H¹_σ(C_c))` Oseen solution `(W, Wq, Wη)` with smooth
BUC drift `V` (`F8Ex.IsSmoothBUCDrift c V`), producing spatially `C^∞`, `c`-periodic,
divergence-free slices `w : ℝ → B0579.Plane → F8Ex.RMerid` in `C((0, 2); H^k(C_c))` for every
`k : ℕ` (`F8Ex.IsRealSpatialSmoothOseenSlices c w W Wq Wη`). Composed in `PartII-b:F8/1/org/2`. -/
def RealCylOseenSpatialBootstrap : Prop :=
  ∀ (c ν : ℝ), 0 < c → 0 < ν →
    ∀ V : ℝ → B0579.Plane → F8Ex.RMerid, F8Ex.IsSmoothBUCDrift c V →
      ∀ (u uq uη : B0579.Plane → F8Ex.RMerid)
        (W Wq Wη : ℝ → B0579.Plane → F8Ex.RMerid),
        F8Ex.IsRealCylH1Datum c u uq uη →
        F8Ex.IsRealWeakH1OseenSol c ν V W Wq Wη u uq uη →
          ∃ w : ℝ → B0579.Plane → F8Ex.RMerid,
            F8Ex.IsRealSpatialSmoothOseenSlices c w W Wq Wη

/-- **Leaf 3 for `PartII-b:F8/1/org/2` (`RealCylOseenJointSmoothUpgrade`, task
`PartII-b:F8/1/org/2/3`, SP 270–288, 2213–2217, 2296–2301)**: joint space-time `C^∞` upgrade on
`(0, 2) × ℝ²`, `(1, ≤2)` slice `L²(cell)` continuity, and `L²_σ(C_c)` residual orthogonality for
spatially smooth `C((0, 2); H^∞(C_c))` Oseen slices `w` driven by the shifted BUC train
`F8Ex.shiftedDriftTrain tr σ` (`tr : B0140.TrainSol ν c`, `PartI.IsBUCTrain tr`, `0 ≤ σ`),
producing `F8Ex.IsRealInteriorSmoothOrbit`. Composed in `PartII-b:F8/1/org/2`. -/
def RealCylOseenJointSmoothUpgrade : Prop :=
  ∀ (c ν : ℝ), 0 < c → 0 < ν →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν c, UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ σ : ℝ, 0 ≤ σ →
        ∀ (u uq uη : B0579.Plane → F8Ex.RMerid)
          (W Wq Wη w : ℝ → B0579.Plane → F8Ex.RMerid),
          F8Ex.IsRealCylH1Datum c u uq uη →
          F8Ex.IsRealWeakH1OseenSol c ν (F8Ex.shiftedDriftTrain tr σ) W Wq Wη u uq uη →
          F8Ex.IsRealSpatialSmoothOseenSlices c w W Wq Wη →
            ∃ W_reg : F8Ex.RProf,
              F8Ex.IsRealInteriorSmoothOrbit c ν (F8Ex.shiftedDriftTrain tr σ) W_reg W Wq Wη

/-- **Conditional assembly of `CylOseenOrbitExists` (`PartII-b:F8/1/org/2`, SP 2213–2217,
2296–2301)** from `RealCylOseenWeakH1Exists`, `RealCylOseenSpatialBootstrap`, and
`RealCylOseenJointSmoothUpgrade`. Composed in task `PartII-b:F8/1/org/2` (`OrbitExists.lean`). -/
theorem cylOseenOrbitExists_of_leaves
    (hEx : RealCylOseenWeakH1Exists)
    (hSp : RealCylOseenSpatialBootstrap)
    (hJt : RealCylOseenJointSmoothUpgrade) :
    UnforcedLeray.Short.IIb.CylOseenOrbitExists := by
  intro dm dp p d hreg σ hσ u uq uη hdat
  have hc : 0 < p.c := p.c_pos
  have hν : 0 < p.ν := p.ν_pos
  have hV : F8Ex.IsSmoothBUCDrift p.c (F8Ex.shiftedDrift p σ) :=
    F8Ex.isSmoothBUCDrift_shiftedDrift hreg hσ
  obtain ⟨hdat_re, hdat_im⟩ := F8Ex.split_cylH1Datum hdat
  obtain ⟨W_re0, Wq_re0, Wη_re0, hwk_re⟩ :=
    hEx p.c p.ν hc hν (F8Ex.shiftedDrift p σ) hV _ _ _ hdat_re
  obtain ⟨w_re, hsp_re⟩ :=
    hSp p.c p.ν hc hν (F8Ex.shiftedDrift p σ) hV _ _ _ W_re0 Wq_re0 Wη_re0 hdat_re hwk_re
  obtain ⟨W_re, hreg_re⟩ :=
    hJt p.c p.ν hc hν p.train hreg.train_buc σ hσ _ _ _ W_re0 Wq_re0 Wη_re0 w_re hdat_re hwk_re
      hsp_re
  obtain ⟨W_im0, Wq_im0, Wη_im0, hwk_im⟩ :=
    hEx p.c p.ν hc hν (F8Ex.shiftedDrift p σ) hV _ _ _ hdat_im
  obtain ⟨w_im, hsp_im⟩ :=
    hSp p.c p.ν hc hν (F8Ex.shiftedDrift p σ) hV _ _ _ W_im0 Wq_im0 Wη_im0 hdat_im hwk_im
  obtain ⟨W_im, hreg_im⟩ :=
    hJt p.c p.ν hc hν p.train hreg.train_buc σ hσ _ _ _ W_im0 Wq_im0 Wη_im0 w_im hdat_im hwk_im
      hsp_im
  have horb_re := F8Ex.realNormalizedOrbit_of_weak_and_reg hwk_re hreg_re
  have horb_im := F8Ex.realNormalizedOrbit_of_weak_and_reg hwk_im hreg_im
  have horb_C := F8Ex.recombine_normalized_orbit hV hdat horb_re horb_im
  exact ⟨fun z => F8Ex.combineMerid (W_re (F8Ex.shiftSub σ z)) (W_im (F8Ex.shiftSub σ z)),
    F8Ex.shift_orbit_from_zero horb_C⟩

end UnforcedLeray.Short.IIb
