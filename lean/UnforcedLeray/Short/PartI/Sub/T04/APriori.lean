import UnforcedLeray.Short.PartI.Sub.T04.Defs
import UnforcedLeray.Short.PartI.Sub.T02.LocalClassicalBounded
import UnforcedLeray.Short.PartI.Tasks.VorticityFirstMoment.CurlRegularity

/-!
# Part I, task `PartI:T04`: the a priori `H³` bound of a classical train on `[0,T]` (conditional)

Source of record: `the November 2 reference manuscript`, lines 278-288: "It is
also the finite-energy solution ... which continues `L²` membership.  Approximation and transverse
cutoffs then give the velocity and vorticity energy identities.  The scalar vorticity equation
preserves zero circulation and its `L¹, L^∞` bounds."

`ClassicalH3APriori`: for `ν > 0`, `c ≥ 1`, `S > 0` there is `B` such that every classical solution
on `[0,T]`, `T ≤ S`, of the class `IsAPrioriClass` (datum `trainDatum c`) has
`‖D^j v(s)‖²_{L²(cell)} ≤ B` for `j ≤ 3` and `s ∈ [0,T]`.  `B` does not depend on `T` or on the
solution; this is what lets the mild train be continued (`Compose.lean`).

It is split along the energy method on the vorticity `ω = curl v`, `ω_s + v·∇ω = νΔω`
(no pressure), with the transverse cutoffs of line 285 and the period-independent cylinder
interpolation of `PartI:T07` (`CylGN`: `‖D^l f‖_{2m/l} ≤ C_m ‖f‖_∞^{1-l/m} ‖D^m f‖₂^{l/m}`,
`CylSupInterp`):

* `APEnergy` (velocity energy identity): `‖v(s)‖₂ ≤ ‖v(0)‖₂`;
* `APEnstrophy` (vorticity energy identity): `‖ω(s)‖₂ ≤ ‖ω(0)‖₂`;
* `APMaxPrinciple` (`L^∞` bound of the scalar vorticity equation): `|ω(s)| ≤ sup|ω(0)|`;
* `APElliptic` (static): `‖D^{j+1} f‖₂² ≤ K_j ‖D^j curl f‖₂²` for divergence-free periodic `f`;
* `APLevel2`: `‖Dω(s)‖₂² ≤ B` from bounds on `‖ω‖₂` and `‖ω‖_∞`;
* `APLevel3`: `‖D²ω(s)‖₂² ≤ B` from bounds on `‖v‖₂`, `‖ω‖₂`, `‖Dω‖₂`, `‖ω‖_∞`.

`classicalH3APriori_of` combines them; the datum constants (`‖trainDatum c‖₂`, `‖curl trainDatum c‖₂`,
`sup |curl trainDatum c|`) depend only on `c`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.B0140 (trainDatum)

/-- **Velocity energy inequality** (lines 278-286, "the velocity ... energy identities"): for a
solution of the class, `‖v(s)‖²_{L²(cell)} ≤ ‖v(0)‖²_{L²(cell)}` on `[0,T]`.  Route: the cutoff
energy `∫_cell χ_R |v|²` (`χ_R = etaCutoff R`), its derivative `-2ν∫χ_R|∇v|²` plus cutoff errors
`O(R^{-1/2})` (viscous cross term, transport `∫χ_R' v_η |v|²`, pressure `∫χ_R' v_η p` with the
pressure bounded by `ClassicalPressureBound`), integrate, `R → ∞` (`JetL2On`). -/
def APEnergy : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p → ∀ s ∈ Icc (0 : ℝ) T, velJet c 0 v s ≤ velJet c 0 v 0

/-- **Vorticity energy inequality** (lines 285-287, "vorticity energy identities", the scalar
vorticity equation): `‖ω(s)‖²_{L²(cell)} ≤ ‖ω(0)‖²_{L²(cell)}` on `[0,T]`.  Route: cutoff energy
`∫χ_R ω²`, `ω_s + v·∇ω = νΔω` (`localVorticityEquation`), the transport term is
`∫χ_R' v_η ω²` (`div v = 0`), integrate, `R → ∞`. -/
def APEnstrophy : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p → ∀ s ∈ Icc (0 : ℝ) T, vortJet c 0 v s ≤ vortJet c 0 v 0

/-- **`L^∞` bound of the vorticity on `[0,T]`** (lines 286-288, "preserves ... its `L^∞`
bounds"): the finite-interval form of `TrainVorticityLinf` (`Sub/PartI_T03.lean`); its proof
(`Tasks/TrainVorticityBounds/Linf.lean`, `linf_core`) only uses the solution on `[0, s+1]`, and runs
verbatim on `[0,T]` (for `s < T`), the case `s = T` by continuity of `ω` (`curlRegularity`). -/
def APMaxPrinciple : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p → ∀ M : ℝ, (∀ z : Plane, |Cyl.curl (v 0) z| ≤ M) →
      ∀ s ∈ Icc (0 : ℝ) T, ∀ z : Plane, |Cyl.curl (v s) z| ≤ M

/-- **Velocity jets from vorticity jets** (static, the elliptic identity behind the vorticity
energy method of lines 285-287): for a smooth `c`-periodic divergence-free field with all
derivatives bounded and in `L²(cell)`, `‖D^{j+1} f‖²₂ ≤ K_j ‖D^j curl f‖²₂`, `K_j` independent of
`f` and `c ≥ 1`.  Route: `∫_cell |∇g|² = ∫_cell (curl g)²` for every derivative word `g = ∂_w f`
(divergence free; integrate `∂_q g_η ∂_η g_q - ∂_q g_q ∂_η g_η` by parts, periodic in `q`, cutoff in
`η`), and the comparison of `‖D^l h‖` with the coordinate words (`cylJetWord_proof`). -/
def APElliptic : Prop :=
  ∀ j : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, 1 ≤ c → ∀ f : Plane → Vec, ContDiff ℝ ∞ f →
    Cyl.IsPeriodic c f → (∀ z, Cyl.divergence f z = 0) →
    (∀ i : ℕ, ∃ M : ℝ, ∀ z, ‖iteratedFDeriv ℝ i f z‖ ≤ M) →
    (∀ i : ℕ, IntegrableOn (fun z => ‖iteratedFDeriv ℝ i f z‖ ^ 2) (Cyl.cell c)) →
    ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ (j + 1) f z‖ ^ 2 ≤
      K * ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ j (Cyl.curl f) z‖ ^ 2

/-- **First vorticity jet** (lines 285-288): given `‖ω(s)‖²₂ ≤ A` and `|ω(s)| ≤ A` on `[0,T]`,
`‖Dω(s)‖²₂ ≤ B(ν, c, S, A)` for `T ≤ S`.  Route: `½ d/ds ‖∇ω‖² = -ν‖Δω‖² - ∫ ∂_iω ∂_iv_j ∂_jω`
(cutoffs, `R → ∞`), `|∫ ∂_iω ∂_iv_j ∂_jω| ≤ ‖∇v‖₂ ‖∇ω‖₄²`, `‖∇v‖₂ ≲ ‖ω‖₂` (`APElliptic`),
`‖∇ω‖₄² ≤ C ‖ω‖_∞ ‖D²ω‖₂` (`CylGN`, `m = 2`, `l = 1`), `‖D²ω‖₂ ≲ ‖Δω‖₂`; Young absorbs `‖Δω‖`,
so `‖∇ω(s)‖² ≤ ‖∇ω(0)‖² + C(ν, A) s`; `ω(0) = curl trainDatum c`. -/
def APLevel2 : Prop :=
  ∀ (ν c S A : ℝ), 0 < ν → 1 ≤ c → 0 < S → ∃ B : ℝ, ∀ (T : ℝ) (v : ℝ → Plane → Vec)
    (p : ℝ → Plane → ℝ), IsAPrioriClass ν c T v p → T ≤ S →
    (∀ s ∈ Icc (0 : ℝ) T, vortJet c 0 v s ≤ A) →
    (∀ s ∈ Icc (0 : ℝ) T, ∀ z : Plane, |Cyl.curl (v s) z| ≤ A) →
    ∀ s ∈ Icc (0 : ℝ) T, vortJet c 1 v s ≤ B

/-- **Second vorticity jet** (lines 285-288): given bounds `A` on `‖v‖²₂`, `‖ω‖²₂`, `‖Dω‖²₂`,
`‖ω‖_∞` on `[0,T]`, `‖D²ω(s)‖²₂ ≤ B(ν, c, S, A)` for `T ≤ S`.  Route:
`½ d/ds ‖∇²ω‖² = -ν‖∇³ω‖² - ∫ ∂²ω · [∂², v·∇]ω`; the commutator terms `∂²v ∇ω`, `∂v ∇∂ω` are
bounded with `CylGN` (`m = 3`) and `‖v‖_∞ ≲ ‖v‖₂ + ‖D²v‖₂` (`CylSupInterp`, `APElliptic`), giving
`d/ds ‖∇²ω‖² ≤ C(ν, A)(1 + ‖∇²ω‖²)`; Gronwall on `[0,S]`. -/
def APLevel3 : Prop :=
  ∀ (ν c S A : ℝ), 0 < ν → 1 ≤ c → 0 < S → ∃ B : ℝ, ∀ (T : ℝ) (v : ℝ → Plane → Vec)
    (p : ℝ → Plane → ℝ), IsAPrioriClass ν c T v p → T ≤ S →
    (∀ s ∈ Icc (0 : ℝ) T, velJet c 0 v s ≤ A) →
    (∀ s ∈ Icc (0 : ℝ) T, vortJet c 0 v s ≤ A) →
    (∀ s ∈ Icc (0 : ℝ) T, vortJet c 1 v s ≤ A) →
    (∀ s ∈ Icc (0 : ℝ) T, ∀ z : Plane, |Cyl.curl (v s) z| ≤ A) →
    ∀ s ∈ Icc (0 : ℝ) T, vortJet c 2 v s ≤ B

/-- **The a priori `H³` bound** (lines 278-288): for `ν > 0`, `c ≥ 1`, `S > 0` there is `B` such
that every solution of the class on `[0,T]`, `T ≤ S`, has `‖D^j v(s)‖²_{L²(cell)} ≤ B` for
`j ≤ 3`, `s ∈ [0,T]`. -/
def ClassicalH3APriori : Prop :=
  ∀ (ν c S : ℝ), 0 < ν → 1 ≤ c → 0 < S → ∃ B : ℝ, ∀ (T : ℝ) (v : ℝ → Plane → Vec)
    (p : ℝ → Plane → ℝ), IsAPrioriClass ν c T v p → T ≤ S →
    ∀ s ∈ Icc (0 : ℝ) T, ∀ j : ℕ, j ≤ 3 → velJet c j v s ≤ B

/-- The slice `v(s)` of a classical solution is smooth. -/
theorem IsClassicalOn.contDiff_slice {ν c T : ℝ} {v : ℝ → Plane → Vec} {p : ℝ → Plane → ℝ}
    (hcl : IsClassicalOn ν c T v p) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) : ContDiff ℝ ∞ (v s) := by
  have h := hcl.smooth_v.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (s := univ) (fun z _ => (⟨hs, mem_univ z⟩ : (s, z) ∈ Icc 0 T ×ˢ univ))
  exact contDiffOn_univ.1 h

/-- **`ClassicalH3APriori` from the six leaves.** -/
theorem classicalH3APriori_of (hE : APEnergy) (hZ : APEnstrophy) (hM : APMaxPrinciple)
    (hK : APElliptic) (h2 : APLevel2) (h3 : APLevel3) : ClassicalH3APriori := by
  intro ν c S hν hc1 hS
  have hc : 0 < c := lt_of_lt_of_le one_pos hc1
  -- the sup of the datum vorticity, read off one local classical solution
  obtain ⟨T₀, hT₀, v₀, p₀, hcl₀, hb₀, -⟩ := localClassicalBounded ν c hν hc1
  obtain ⟨-, -, ⟨M₀, hM₀⟩, -⟩ :=
    curlRegularity c T₀ v₀ hc hT₀ hcl₀.smooth_v hcl₀.periodic_v hb₀
  have hM₀' : ∀ z : Plane, |Cyl.curl (trainDatum c) z| ≤ M₀ := by
    intro z
    have h := hM₀ 0 ⟨le_rfl, hT₀.le⟩ z
    rwa [hcl₀.initial] at h
  obtain ⟨A, hEA, hZA, hMA⟩ : ∃ A : ℝ,
      (∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 0 (trainDatum c) z‖ ^ 2) ≤ A ∧
      (∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 0 (Cyl.curl (trainDatum c)) z‖ ^ 2) ≤ A ∧
      M₀ ≤ A :=
    ⟨max (max _ _) M₀, le_trans (le_max_left _ _) (le_max_left _ _),
      le_trans (le_max_right _ _) (le_max_left _ _), le_max_right _ _⟩
  obtain ⟨B₂, hB₂⟩ := h2 ν c S A hν hc1 hS
  obtain ⟨B₃, hB₃⟩ := h3 ν c S (max A B₂) hν hc1 hS
  obtain ⟨K₀, hK₀, hK₀'⟩ := hK 0
  obtain ⟨K₁, hK₁, hK₁'⟩ := hK 1
  obtain ⟨K₂, hK₂, hK₂'⟩ := hK 2
  refine ⟨max (max A (K₀ * A)) (max (K₁ * B₂) (K₂ * B₃)), ?_⟩
  intro T v p hcls hTS
  have hv0 : v 0 = trainDatum c := hcls.classical.initial
  have hEs : ∀ s ∈ Icc (0 : ℝ) T, velJet c 0 v s ≤ A := by
    intro s hs
    have h := hE ν c T v p hν hc1 hcls s hs
    unfold velJet at h ⊢
    rw [hv0] at h
    exact h.trans hEA
  have hZs : ∀ s ∈ Icc (0 : ℝ) T, vortJet c 0 v s ≤ A := by
    intro s hs
    have h := hZ ν c T v p hν hc1 hcls s hs
    unfold vortJet at h ⊢
    rw [hv0] at h
    exact h.trans hZA
  have hMs : ∀ s ∈ Icc (0 : ℝ) T, ∀ z : Plane, |Cyl.curl (v s) z| ≤ A := by
    intro s hs z
    have h := hM ν c T v p hν hc1 hcls M₀ (fun z => by rw [hv0]; exact hM₀' z) s hs z
    exact h.trans hMA
  have h2s : ∀ s ∈ Icc (0 : ℝ) T, vortJet c 1 v s ≤ B₂ := hB₂ T v p hcls hTS hZs hMs
  have h3s : ∀ s ∈ Icc (0 : ℝ) T, vortJet c 2 v s ≤ B₃ :=
    hB₃ T v p hcls hTS (fun s hs => (hEs s hs).trans (le_max_left _ _))
      (fun s hs => (hZs s hs).trans (le_max_left _ _))
      (fun s hs => (h2s s hs).trans (le_max_right _ _))
      (fun s hs z => (hMs s hs z).trans (le_max_left _ _))
  intro s hs j hj
  have hsm : ContDiff ℝ ∞ (v s) := hcls.classical.contDiff_slice hs
  have hper : Cyl.IsPeriodic c (v s) := hcls.classical.periodic_v s hs
  have hdiv : ∀ z, Cyl.divergence (v s) z = 0 := hcls.classical.solenoidal s hs
  have hbd : ∀ i : ℕ, ∃ M : ℝ, ∀ z, ‖iteratedFDeriv ℝ i (v s) z‖ ≤ M := by
    intro i
    obtain ⟨M, hM'⟩ := hcls.bounded i
    exact ⟨M, hM' s hs⟩
  have hint : ∀ i : ℕ, IntegrableOn (fun z => ‖iteratedFDeriv ℝ i (v s) z‖ ^ 2) (Cyl.cell c) := by
    intro i
    obtain ⟨K, hK'⟩ := hcls.jet_l2 i
    exact (hK' s hs).1
  interval_cases j
  · exact (hEs s hs).trans (le_trans (le_max_left _ _) (le_max_left _ _))
  · have h := hK₀' c hc1 (v s) hsm hper hdiv hbd hint
    calc velJet c 1 v s ≤ K₀ * vortJet c 0 v s := h
      _ ≤ K₀ * A := mul_le_mul_of_nonneg_left (hZs s hs) hK₀
      _ ≤ _ := le_trans (le_max_right _ _) (le_max_left _ _)
  · have h := hK₁' c hc1 (v s) hsm hper hdiv hbd hint
    calc velJet c 2 v s ≤ K₁ * vortJet c 1 v s := h
      _ ≤ K₁ * B₂ := mul_le_mul_of_nonneg_left (h2s s hs) hK₁
      _ ≤ _ := le_trans (le_max_left _ _) (le_max_right _ _)
  · have h := hK₂' c hc1 (v s) hsm hper hdiv hbd hint
    calc velJet c 3 v s ≤ K₂ * vortJet c 2 v s := h
      _ ≤ K₂ * B₃ := mul_le_mul_of_nonneg_left (h3s s hs) hK₂
      _ ≤ _ := le_trans (le_max_right _ _) (le_max_right _ _)

end UnforcedLeray.Short.PartI
