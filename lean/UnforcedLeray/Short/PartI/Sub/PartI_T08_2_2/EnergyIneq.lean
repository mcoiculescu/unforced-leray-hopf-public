import UnforcedLeray.Short.PartI.Sub.PartI_T08_2_2

/-!
# Part I, task `PartI:T08/2/2/2` (`VortJetEnergyIneq`): decomposition

Source of record: `the November 2 reference manuscript`, lines 276-288 (the train
is the `BUC` solution, smooth for positive time; "Approximation and transverse cutoffs then give
the velocity and vorticity energy identities. The scalar vorticity equation ...").

Target `VortJetEnergyIneq` (`Sub/PartI_T08_2_2.lean`): for a BUC train, `j` and `S > 0` there is
`C ≥ 0` with, for all `R ≥ 1`, `F_R = vortJetEnergy tr j R` continuous on `[0, S]` and
`F_R' ≤ C F_R + C` on `(0, S)`.

## Mathematics (`ω = curl v`, `Ω_u = ∂_u ω`, `χ = χ_R = etaCutoff R`)

`ω_s + v·∇ω = νΔω` (curl of the momentum equation, `B0238.vorticityResidual_eq_zero`), hence
`∂_s Ω_u = νΔΩ_u - ∂_u(v·∇ω)` (`VortWordEquation`).  Differentiating under the integral
(`CutoffJetHasDeriv`, compact support in `|η| ≤ 2R`),
`F_R' = ν ∫ χ Σ_u 2Ω_u ΔΩ_u - ∫ χ Σ_u 2Ω_u ∂_u(v·∇ω)`.  With `M` bounding all words of `v` of
order `≤ j + 2` on `[0, S]` (`IsBUCTrain`):
* viscous: `∫ χ 2Ω ΔΩ = -2∫ χ|∇Ω|² - 2∫ χ' Ω ∂_ηΩ ≤ 2(C₀/R) M² · 2Rc` (`CutoffJetViscousBound`);
* transport: `∂_u(v·∇ω) = v·∇Ω_u + [∂_u, v·∇]ω`, `-∫ χ 2Ω (v·∇Ω) = ∫ χ' v_η Ω² = O(cM³)`
  (`div v = 0`, `CutoffAdvTop`), and `|[∂_u, v·∇]ω| ≤ K M Σ_{|u'| ≤ j} |Ω_{u'}|` (Leibniz,
  `WordAdvCommutator`), so the transport sum is `≤ K F_R + K` (`CutoffJetTransportBound`).

`vortJetEnergyIneq_of` derives `VortJetEnergyIneq` from `SliceWordReg`, `CutoffJetContinuous`,
`CutoffJetHasDeriv`, `VortWordEquation`, `CutoffJetViscousBound`, `CutoffJetTransportBound`.
`VortWordEquation` rests on `SliceWordTimeComm` and `DerivWordLapComm`;
`CutoffJetTransportBound` on `WordAdvCommutator` and `CutoffAdvTop`.  Every leaf except
`VortWordEquation` is a statement about arbitrary smooth functions.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-- The scalar transport `b·∇h = b_q ∂_q h + b_η ∂_η h` (components `0 = q`, `1 = η`). -/
def scalarAdv (b : Plane → Vec) (h : Plane → ℝ) (z : Plane) : ℝ :=
  b z 0 * Cyl.partialQ h z + b z 1 * Cyl.partialEta h z

/-! ### Leaves: calculus of slices -/

/-- **Toolkit leaf (moving a letter through a word, Schwarz)** (calculus).  For smooth `f`,
`∂_b ∂_u f = ∂_u ∂_b f`: `derivWord (b :: u) f = derivWord (u ++ [b]) f`.  Route: induction on
`u`, using that two coordinate partials of a smooth function commute
(`B0151.partialX_eq_fderiv`, `B0151.partialY_eq_fderiv`, `ContDiff.fderiv_right`,
`fderiv_clm_apply`, `ContDiffAt.isSymmSndFDerivAt`; cf. `LV.lvDir_symm`) and
`B0151.contDiff_derivWord`.  Used by `DerivWordLapComm`, `WordAdvCommutator` and
`TrainVelocityWordLap`. -/
def DerivWordConsAppend : Prop :=
  ∀ f : Plane → ℝ, ContDiff ℝ ∞ f → ∀ (b : Bool) (u : List Bool),
    B0151.derivWord (b :: u) f = B0151.derivWord (u ++ [b]) f

/-- **Leaf (joint regularity of spatial words up to `s = 0`)** (calculus).  If `F` is `C^∞` on
`[0, ∞) × ℝ²` (`ContDiffOn` on the closed half-space, as `B0140.IsTrain.smooth_v`), then every
spatial word derivative `(s, z) ↦ ∂_u [F(s, ·)](z)` is `C^∞` on `[0, ∞) × ℝ²`.  Route: induction on
`u`; `Ici 0 ×ˢ univ` is `UniqueDiffOn` (convex, nonempty interior); the line
`t ↦ (s, (t, η))` stays in the set, so `∂_q [G(s, ·)](z) = fderivWithin ℝ G (Ici 0 ×ˢ univ) (s, z)
(0, (1, 0))` (`HasFDerivWithinAt.comp_hasDerivAt`-type composition), and
`ContDiffOn.fderivWithin` with `ContDiffOn.clm_apply`, then `ContDiffOn.congr`. -/
def SliceWordReg : Prop :=
  ∀ F : ℝ × Plane → ℝ, ContDiffOn ℝ ∞ F (Ici 0 ×ˢ univ) → ∀ u : List Bool,
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => B0151.derivWord u (fun z => F (x.1, z)) x.2)
      (Ici 0 ×ˢ univ)

/-- **Leaf (time derivative commutes with spatial words)** (calculus, symmetry of mixed
derivatives on the open set `(0, ∞) × ℝ²`).  For `F` smooth on `(0, ∞) × ℝ²` and `s > 0`:
`∂_s ∂_u [F(s, ·)](z) = ∂_u [∂_s F(s, ·)](z)`.  Route: the space-time layer of
`Tasks/VorticityFirstMoment/LocalVorticityEquation/Layer.lean` (`lvDir`, `lvDir_symm`,
`lvSliceQ/E/T`) with `O = Ioi 0 ×ˢ univ`; induction on `u`, writing each word as an iterated
`lvDir` of `F` and commuting `lvEt` through. -/
def SliceWordTimeComm : Prop :=
  ∀ F : ℝ × Plane → ℝ, ContDiffOn ℝ ∞ F (Ioi 0 ×ˢ univ) →
    ∀ (u : List Bool) (s : ℝ) (z : Plane), 0 < s →
      deriv (fun t => B0151.derivWord u (fun z' => F (t, z')) z) s =
        B0151.derivWord u (fun z' => deriv (fun t => F (t, z')) s) z

/-- **Leaf (spatial words commute with the Laplacian)** (calculus).  For smooth `h`,
`∂_u Δh = Δ∂_u h`.  Route: `Train.lapS h = ∂_q∂_q h + ∂_η∂_η h`; `derivWord` is additive on
smooth functions (`ForcingIBP.derivWord_add_smooth`) and two coordinate partials commute on
smooth functions (`B0151.partialX_eq_fderiv`, `ContDiffAt.isSymmSndFDerivAt`); induction on
`u`. -/
def DerivWordLapComm : Prop :=
  ∀ h : Plane → ℝ, ContDiff ℝ ∞ h → ∀ u : List Bool,
    B0151.derivWord u (Train.lapS h) = Train.lapS (B0151.derivWord u h)

/-- **Leaf (the differentiated vorticity equation)** (lines 276-288; the scalar vorticity
equation, line 286).  For a train and `s > 0`:
`∂_s ∂_u ω(s, z) = ν Δ∂_u ω(s, z) - ∂_u (v·∇ω)(s, z)`.  Route: `B0238.vorticityResidual_eq_zero`
(from `smooth_v`, `smooth_p`, `solenoidal`, `momentum`) gives `∂_s ω = νΔω - v·∇ω` for all `z` at
every `s > 0`; `SliceWordTimeComm` for `F(x) = curl (v x.1) x.2` (smooth on `Ioi 0 ×ˢ univ`:
`vortWord_eq`, `SliceWordReg`-type argument or the `B0238` `sm_*` lemmas) moves `∂_s` inside
`∂_u`; `derivWord` is linear on smooth functions; `DerivWordLapComm`. -/
def VortWordEquation : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : B0140.TrainSol ν c, ∀ s : ℝ, 0 < s →
    ∀ (u : List Bool) (z : Plane),
      deriv (fun t => vortWord tr u t z) s =
        ν * Train.lapS (vortWord tr u s) z -
          B0151.derivWord u (scalarAdv (tr.v s) (Cyl.curl (tr.v s))) z

/-! ### Leaves: the cutoff integral -/

/-- **Leaf (continuity of the cutoff jet energy)** (measure theory).  If every `W u` (`u ∈ ι`) is
continuous on `[0, ∞) × ℝ²`, then `s ↦ ∫_cell χ_R Σ_u W u (s, z)²` is continuous on `[0, S]`.
Route: as `Tasks/TrainCutoffEnergyProof/Continuity.lean` (`cutoffEnergyContinuous`): the
integrand is continuous on `[0, S] × ([-c/2, c/2] × [-2R, 2R])` (compact, hence bounded) and
vanishes for `|η| ≥ 2R`; `continuousOn_of_dominated` / `continuousWithinAt_of_dominated`. -/
def CutoffJetContinuous : Prop :=
  ∀ (c R S : ℝ) (ι : Finset (List Bool)) (W : List Bool → ℝ × Plane → ℝ), 0 < c → 0 < R →
    (∀ u ∈ ι, ContinuousOn (W u) (Ici 0 ×ˢ univ)) →
    ContinuousOn (fun s => ∫ z in Cyl.cell c, etaCutoff R z.2 * ∑ u ∈ ι, W u (s, z) ^ 2)
      (Icc 0 S)

/-- **Leaf (differentiation of the cutoff jet energy)** (measure theory).  If every `W u` is `C^∞`
on `(0, ∞) × ℝ²`, the cutoff jet energy is differentiable at `t₀ > 0` with derivative
`∫_cell χ_R Σ_u 2 W_u ∂_t W_u`.  Route: `cehd_generic`
(`Tasks/TrainCutoffEnergyProof/HasDeriv.lean`) for a scalar finite sum of squares:
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` with the bound `1_{box} · max C 0` on
`[t₀/2, 2t₀] × cehdBox c R`. -/
def CutoffJetHasDeriv : Prop :=
  ∀ (c R : ℝ) (ι : Finset (List Bool)) (W : List Bool → ℝ × Plane → ℝ), 0 < c → 0 < R →
    (∀ u ∈ ι, ContDiffOn ℝ ∞ (W u) (Ioi 0 ×ˢ univ)) → ∀ t₀ : ℝ, 0 < t₀ →
    HasDerivAt (fun t => ∫ z in Cyl.cell c, etaCutoff R z.2 * ∑ u ∈ ι, W u (t, z) ^ 2)
      (∫ z in Cyl.cell c, etaCutoff R z.2 *
        ∑ u ∈ ι, 2 * W u (t₀, z) * deriv (fun t => W u (t, z)) t₀) t₀

/-! ### Leaves: the two estimates -/

/-- **Leaf (viscous term)** (lines 286-287, transverse cutoff).  For a smooth `c`-periodic `h`
whose words of length `≤ j + 1` are bounded by `M`: `∫_cell χ_R Σ_{|u| ≤ j} 2 ∂_uh Δ∂_uh ≤ K`,
`K` independent of `R ≥ 1` and `h`.  Route, for each `g = ∂_u h`: cell integration by parts
(`CellDerivZero` for `χ_R g ∂_q g`, `χ_R g ∂_η g`, which vanish for `|η| ≥ 2R`) gives
`∫ χ g Δg = -∫ χ (|∂_q g|² + |∂_η g|²) - ∫ χ' g ∂_η g ≤ ∫ |χ'| M²`, and
`|χ'| ≤ C₀/R` on `R ≤ |η| ≤ 2R` (`etaCutoffFacts`), a set of cell area `2Rc`; so
`K = 2 · #wordsUpTo j · 2C₀ c M²`. -/
def CutoffJetViscousBound : Prop :=
  ∀ (j : ℕ) (c M : ℝ), 0 < c → ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R → ∀ h : Plane → ℝ,
    ContDiff ℝ ∞ h → Cyl.IsPeriodic c h →
    (∀ u : List Bool, u.length ≤ j + 1 → ∀ z : Plane, |B0151.derivWord u h z| ≤ M) →
    ∫ z in Cyl.cell c, etaCutoff R z.2 *
      ∑ u ∈ wordsUpTo j, 2 * B0151.derivWord u h z * Train.lapS (B0151.derivWord u h) z ≤ K

/-- **Leaf (the transport commutator, pointwise Leibniz)** (calculus; lines 352-353 use the same
commutator `[D^j, e·∇]`).  If the words of `b` of length `≤ j` are bounded by `M`, then for
`|u| ≤ j`: `|∂_u(b·∇h) - b·∇∂_u h| ≤ K M Σ_{|u'| ≤ j} |∂_{u'} h|`, `K` depending only on `j`.
Route: Leibniz for `derivWord` of a product (sum over the `2^{|u|}` splittings of `u`, induction
on `u` with the product rule for `partialX/partialY`); the splitting with all letters on `h` is
`b_i ∂_u ∂_i h = b_i ∂_i ∂_u h` (partials commute on smooth `h`); every other term is
`∂_a b_i · ∂_{a'} ∂_i h` with `|a| ≥ 1`, `|a'| + 1 ≤ |u| ≤ j`. -/
def WordAdvCommutator : Prop :=
  ∀ j : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (M : ℝ) (b : Plane → Vec) (h : Plane → ℝ),
    ContDiff ℝ ∞ b → ContDiff ℝ ∞ h →
    (∀ (u : List Bool) (k : Fin 2), u.length ≤ j → ∀ z : Plane, |wordComp u b k z| ≤ M) →
    ∀ u : List Bool, u.length ≤ j → ∀ z : Plane,
      |B0151.derivWord u (scalarAdv b h) z - scalarAdv b (B0151.derivWord u h) z| ≤
        K * M * ∑ u' ∈ wordsUpTo j, |B0151.derivWord u' h z|

/-- **Leaf (the top transport term, cutoff integration by parts)** (lines 286-287).  For a smooth
`c`-periodic divergence-free `b` with `|b_η| ≤ M` and a smooth `c`-periodic `g` with `|g| ≤ M`:
`-∫_cell χ_R 2g (b·∇g) ≤ K₀ c M³`, `K₀` absolute.  Route: `2g (b·∇g) = b·∇(g²)` and
`div(χ_R g² b) = χ_R b·∇(g²) + χ_R' b_η g²` (`div b = 0`); `CellDerivZero` (the field vanishes for
`|η| ≥ 2R`) gives `-∫ χ_R b·∇(g²) = ∫ χ_R' b_η g² ≤ (C₀/R) M³ · 2Rc`. -/
def CutoffAdvTop : Prop :=
  ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ (c R M : ℝ) (b : Plane → Vec) (g : Plane → ℝ), 0 < c → 1 ≤ R →
    ContDiff ℝ ∞ b → ContDiff ℝ ∞ g → Cyl.IsPeriodic c b → Cyl.IsPeriodic c g →
    (∀ z : Plane, Cyl.divergence b z = 0) → (∀ z : Plane, |b z 1| ≤ M) →
    (∀ z : Plane, |g z| ≤ M) →
    -(∫ z in Cyl.cell c, etaCutoff R z.2 * (2 * g z * scalarAdv b g z)) ≤ K₀ * c * M ^ 3

/-- **Leaf (transport term of the jet energy)** (lines 286-287).  For a smooth `c`-periodic
divergence-free `b` with words of length `≤ j` bounded by `M`, and a smooth `c`-periodic `h` with
words of length `≤ j` bounded by `M`:
`-∫_cell χ_R Σ_{|u| ≤ j} 2 ∂_uh ∂_u(b·∇h) ≤ K ∫_cell χ_R Σ_{|u| ≤ j} (∂_uh)² + K`, `K` independent
of `R ≥ 1`, `b`, `h`.  Route: split `∂_u(b·∇h) = b·∇∂_uh + [∂_u, b·∇]h`; `CutoffAdvTop` for each
`g = ∂_uh` gives `N K₀ c M³` (`N = #wordsUpTo j`); `WordAdvCommutator` and
`(Σ_u |x_u|)² ≤ N Σ_u x_u²` give `2 K_j M N ∫ χ_R Σ_u (∂_uh)²`.  All integrands are continuous and
vanish for `|η| ≥ 2R` (`cellIntegrable_aux`), so the integral of the sum splits. -/
def CutoffJetTransportBound : Prop :=
  ∀ (j : ℕ) (c M : ℝ), 0 < c → ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R →
    ∀ (b : Plane → Vec) (h : Plane → ℝ), ContDiff ℝ ∞ b → ContDiff ℝ ∞ h →
    Cyl.IsPeriodic c b → Cyl.IsPeriodic c h → (∀ z : Plane, Cyl.divergence b z = 0) →
    (∀ (u : List Bool) (k : Fin 2), u.length ≤ j → ∀ z : Plane, |wordComp u b k z| ≤ M) →
    (∀ u : List Bool, u.length ≤ j → ∀ z : Plane, |B0151.derivWord u h z| ≤ M) →
    -(∫ z in Cyl.cell c, etaCutoff R z.2 *
        ∑ u ∈ wordsUpTo j, 2 * B0151.derivWord u h z * B0151.derivWord u (scalarAdv b h) z) ≤
      K * (∫ z in Cyl.cell c, etaCutoff R z.2 * ∑ u ∈ wordsUpTo j, B0151.derivWord u h z ^ 2)
        + K

/-! ### Helpers -/

theorem vjl_lapS_contDiff {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (Train.lapS g) :=
  (B0151.contDiff_derivWord hg [true, true]).add (B0151.contDiff_derivWord hg [false, false])

theorem vjl_scalarAdv_contDiff {b : Plane → Vec} {h : Plane → ℝ} (hb : ContDiff ℝ ∞ b)
    (hh : ContDiff ℝ ∞ h) : ContDiff ℝ ∞ (scalarAdv b h) := by
  have hb0 : ContDiff ℝ ∞ (fun z => b z 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hb
  have hb1 : ContDiff ℝ ∞ (fun z => b z 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hb
  have hq : ContDiff ℝ ∞ (Cyl.partialQ h) := B0151.contDiff_derivWord hh [true]
  have he : ContDiff ℝ ∞ (Cyl.partialEta h) := B0151.contDiff_derivWord hh [false]
  exact (hb0.mul hq).add (hb1.mul he)

/-- One bound `M ≥ 0` for all velocity words of length `≤ n` on `[0, S]`. -/
theorem vjl_uniform_wordBound {ν c : ℝ} {tr : B0140.TrainSol ν c} (htr : IsBUCTrain tr) {S : ℝ}
    (hS : 0 ≤ S) (n : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ u : List Bool, u.length ≤ n → ∀ k : Fin 2,
      ∀ s ∈ Icc (0 : ℝ) S, ∀ z : Plane, |wordComp u (tr.v s) k z| ≤ M := by
  choose f hf using fun (u : List Bool) (k : Fin 2) => vjl_wordBoundedOn htr hS u k
  refine ⟨∑ u ∈ wordsUpTo n, ∑ k : Fin 2, |f u k|,
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)), ?_⟩
  intro u hu k s hs z
  calc |wordComp u (tr.v s) k z| ≤ f u k := hf u k s hs z
    _ ≤ |f u k| := le_abs_self _
    _ ≤ ∑ k' : Fin 2, |f u k'| :=
        Finset.single_le_sum (f := fun k' => |f u k'|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ k)
    _ ≤ ∑ u' ∈ wordsUpTo n, ∑ k' : Fin 2, |f u' k'| :=
        Finset.single_le_sum (f := fun u' => ∑ k' : Fin 2, |f u' k'|)
          (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (mem_wordsUpTo.2 hu)

/-- The vorticity words are jointly `C^∞` on `[0, ∞) × ℝ²`. -/
theorem vjl_vortWord_joint (hReg : SliceWordReg) {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (u : List Bool) :
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => vortWord tr u x.1 x.2) (Ici 0 ×ˢ univ) := by
  have hF : ∀ k : Fin 2, ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2 k) (Ici 0 ×ˢ univ) :=
    fun k => (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp_contDiffOn
      tr.isTrain.smooth_v
  have h1 := hReg _ (hF 1) (u ++ [true])
  have h0 := hReg _ (hF 0) (u ++ [false])
  refine (h1.sub h0).congr (fun x hx => ?_)
  exact vortWord_eq tr hx.1 u x.2

theorem vjl_curl_periodic {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s) :
    Cyl.IsPeriodic c (Cyl.curl (tr.v s)) := by
  intro z
  have e1 : Cyl.curl (tr.v s) (z.1 + c, z.2) = _ := vortWord_eq tr hs [] (z.1 + c, z.2)
  have e2 : Cyl.curl (tr.v s) z = _ := vortWord_eq tr hs [] z
  rw [e1, e2, vjl_word_periodic tr hs ([] ++ [true]) 1 z,
    vjl_word_periodic tr hs ([] ++ [false]) 0 z]

theorem vjl_sum_alg (ι : Finset (List Bool)) (χ ν : ℝ) (a l d : List Bool → ℝ) :
    χ * ∑ u ∈ ι, 2 * a u * (ν * l u - d u) =
      ν * (χ * ∑ u ∈ ι, 2 * a u * l u) - χ * ∑ u ∈ ι, 2 * a u * d u := by
  simp only [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun u _ => by ring)

/-! ### The conditional theorem -/

/-- **`VortJetEnergyIneq` from the leaves.** -/
theorem vortJetEnergyIneq_of (hReg : SliceWordReg) (hCont : CutoffJetContinuous)
    (hDer : CutoffJetHasDeriv) (hEq : VortWordEquation) (hVisc : CutoffJetViscousBound)
    (hTr : CutoffJetTransportBound) : VortJetEnergyIneq := by
  intro ν c hν hc tr htr j S hS
  have hc0 : 0 < c := by linarith
  obtain ⟨M, hM0, hM⟩ := vjl_uniform_wordBound htr hS.le (j + 2)
  have hvort : ∀ u : List Bool, u.length ≤ j + 1 → ∀ s ∈ Icc (0 : ℝ) S, ∀ z : Plane,
      |B0151.derivWord u (Cyl.curl (tr.v s)) z| ≤ 2 * M := by
    intro u hu s hs z
    have e : B0151.derivWord u (Cyl.curl (tr.v s)) z = _ := vortWord_eq tr hs.1 u z
    rw [e]
    have hl1 : (u ++ [true]).length ≤ j + 2 := by simp only [List.length_append, List.length_singleton]; omega
    have hl0 : (u ++ [false]).length ≤ j + 2 := by simp only [List.length_append, List.length_singleton]; omega
    have a1 := hM _ hl1 1 s hs z
    have a0 := hM _ hl0 0 s hs z
    calc |wordComp (u ++ [true]) (tr.v s) 1 z - wordComp (u ++ [false]) (tr.v s) 0 z|
        ≤ |wordComp (u ++ [true]) (tr.v s) 1 z| + |wordComp (u ++ [false]) (tr.v s) 0 z| :=
          abs_sub _ _
      _ ≤ 2 * M := by linarith
  have hvel : ∀ (u : List Bool) (k : Fin 2), u.length ≤ j → ∀ s ∈ Icc (0 : ℝ) S, ∀ z : Plane,
      |wordComp u (tr.v s) k z| ≤ 2 * M := by
    intro u k hu s hs z
    exact (hM u (by omega) k s hs z).trans (by linarith)
  obtain ⟨K₁, hK₁, hV⟩ := hVisc j c (2 * M) hc0
  obtain ⟨K₂, hK₂, hT⟩ := hTr j c (2 * M) hc0
  refine ⟨ν * K₁ + K₂, add_nonneg (mul_nonneg hν.le hK₁) hK₂, fun R hR => ?_⟩
  have hR0 : 0 < R := by linarith
  have hjoint := fun u => vjl_vortWord_joint hReg tr u
  refine ⟨?_, fun s hs => ?_⟩
  · exact hCont c R S (wordsUpTo j) (fun u x => vortWord tr u x.1 x.2) hc0 hR0
      (fun u _ => (hjoint u).continuousOn)
  · have hs0 : 0 < s := hs.1
    have hsI : s ∈ Icc (0 : ℝ) S := ⟨hs.1.le, hs.2.le⟩
    have hd : HasDerivAt (vortJetEnergy tr j R)
        (∫ z in Cyl.cell c, etaCutoff R z.2 *
          ∑ u ∈ wordsUpTo j, 2 * vortWord tr u s z * deriv (fun t => vortWord tr u t z) s) s :=
      hDer c R (wordsUpTo j) (fun u x => vortWord tr u x.1 x.2) hc0 hR0
        (fun u _ => (hjoint u).mono (prod_mono Ioi_subset_Ici_self subset_rfl)) s hs0
    refine ⟨_, hd, ?_⟩
    have hv : ContDiff ℝ ∞ (tr.v s) :=
      TrainErrorEquation.contDiff_slice tr.isTrain.smooth_v hs0.le
    have hω : ContDiff ℝ ∞ (Cyl.curl (tr.v s)) := vjl_vortWord_contDiff tr hs0.le []
    have hA : ContDiff ℝ ∞ (scalarAdv (tr.v s) (Cyl.curl (tr.v s))) :=
      vjl_scalarAdv_contDiff hv hω
    have hc₁ : Continuous (fun z => ∑ u ∈ wordsUpTo j,
        2 * vortWord tr u s z * Train.lapS (vortWord tr u s) z) :=
      continuous_finsetSum _ (fun u _ =>
        (continuous_const.mul (vjl_vortWord_contDiff tr hs0.le u).continuous).mul
          (vjl_lapS_contDiff (vjl_vortWord_contDiff tr hs0.le u)).continuous)
    have hc₂ : Continuous (fun z => ∑ u ∈ wordsUpTo j, 2 * vortWord tr u s z *
        B0151.derivWord u (scalarAdv (tr.v s) (Cyl.curl (tr.v s))) z) :=
      continuous_finsetSum _ (fun u _ =>
        (continuous_const.mul (vjl_vortWord_contDiff tr hs0.le u).continuous).mul
          (B0151.contDiff_derivWord hA u).continuous)
    have hi₁ := vjl_cutoff_integrable (c := c) hR0 hc₁
    have hi₂ := vjl_cutoff_integrable (c := c) hR0 hc₂
    have hfun : (fun z => etaCutoff R z.2 *
          ∑ u ∈ wordsUpTo j, 2 * vortWord tr u s z * deriv (fun t => vortWord tr u t z) s) =
        fun z => ν * (etaCutoff R z.2 * ∑ u ∈ wordsUpTo j,
            2 * vortWord tr u s z * Train.lapS (vortWord tr u s) z) -
          etaCutoff R z.2 * ∑ u ∈ wordsUpTo j, 2 * vortWord tr u s z *
            B0151.derivWord u (scalarAdv (tr.v s) (Cyl.curl (tr.v s))) z := by
      funext z
      rw [Finset.sum_congr rfl (fun u _ => by rw [hEq ν c hν hc0 tr s hs0 u z])]
      exact vjl_sum_alg _ _ _ _ _ _
    rw [hfun, integral_sub (hi₁.const_mul ν) hi₂, integral_const_mul]
    have b₁ : ∫ z in Cyl.cell c, etaCutoff R z.2 * ∑ u ∈ wordsUpTo j,
        2 * vortWord tr u s z * Train.lapS (vortWord tr u s) z ≤ K₁ :=
      hV R hR (Cyl.curl (tr.v s)) hω (vjl_curl_periodic tr hs0.le)
        (fun u hu z => hvort u hu s hsI z)
    have b₂ : -(∫ z in Cyl.cell c, etaCutoff R z.2 * ∑ u ∈ wordsUpTo j, 2 * vortWord tr u s z *
        B0151.derivWord u (scalarAdv (tr.v s) (Cyl.curl (tr.v s))) z) ≤
          K₂ * vortJetEnergy tr j R s + K₂ :=
      hT R hR (tr.v s) (Cyl.curl (tr.v s)) hv hω (tr.isTrain.periodic_v s hs0.le)
        (vjl_curl_periodic tr hs0.le) (tr.isTrain.solenoidal s hs0.le)
        (fun u k hu z => hvel u k hu s hsI z)
        (fun u hu z => hvort u (by omega) s hsI z)
    have hF0 : 0 ≤ vortJetEnergy tr j R s :=
      integral_nonneg (fun z => mul_nonneg (etaCutoff_nonneg R z.2)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    have hνb : ν * (∫ z in Cyl.cell c, etaCutoff R z.2 * ∑ u ∈ wordsUpTo j,
        2 * vortWord tr u s z * Train.lapS (vortWord tr u s) z) ≤ ν * K₁ :=
      mul_le_mul_of_nonneg_left b₁ hν.le
    nlinarith [mul_nonneg (mul_nonneg hν.le hK₁) hF0]

end UnforcedLeray.Short.PartI
