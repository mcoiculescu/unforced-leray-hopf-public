import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Defs
import UnforcedLeray.Lib.CylinderB.BiotSavart

/-!
# `PartIII-a:T21/2/7/2/1/1/2`: the weighted space-time jets of the train (vocabulary, leaves)

Source of record: `the November 2 reference manuscript` (SP), lines 261-266
(`v = ∇^⊥ψ`, the train), 270-288 (the Gallay-Slijepčević train: unique global mild solution in
`BUC`, smooth for positive time; the scalar vorticity equation preserves zero circulation;
`v(-q,-η,s) = -v(q,η,s)`), 438-461 (`sct:heat`: every fixed mixed age/spatial derivative, weighted,
at fixed parameters), 2866-2870 (every fixed weighted derivative norm), 2081-2084 (`E_c = curl v_c`;
`K_c`, the cylinder Biot-Savart operator, includes the horizontal mean mode).

## The target

`TrainSTJetsOfBUC m` (`Sub/AdjInterior/Defs.lean`): for `0 < ν ≤ 1`, `c = ν⁻²`, a train in the
`BUC` class with the bounds `LadTrainBdd` on every `[0, S]` has, on every `[0, S] × ℝ²`, all joint
`(ρ, x)`-derivatives of `v` bounded and all joint derivatives of positive order of `E = curl v`
bounded with the weight `(1 + x₂²)^{(m+1)/2}` (`TrainSTJets`).

## The route

All derivatives are iterated directional derivatives within `[0, ∞) × ℝ²` (`tjU`) along the
coordinate directions `stDir` (`0` the age, `1, 2` space): `tjW L h` for a word `L`.
1. **Jets from words** (`TjJetNorm`, calculus): `‖D^n h(p)‖ ≤ K Σ_{|L| = n} ‖tjW L h p‖`.
2. **Words with no age letter** (`TjTrainSpace m`, assembled in `Assembly.lean` from
   `TjSliceNorm`, `TjSpatialInterp`, `TjVortDecay`, `TjLadGrad`, `TjTrainVort`, `TjWLinear`):
   the spatial words of `v` are bounded (`IsBUCTrain`); those of `∇E` are weighted by
   interpolation (`TjSpatialInterp`: `(1 + x₂²)^{(m+2)/2}|∇E| ≤ C` from `LadTrainBdd`, `TjLadGrad`,
   against the unweighted bounds of all higher words, exponent `m + 1 < m + 2`); `E` itself decays
   (`TjVortDecay`, from `TjDecayOfGrad` and `TjCirculationBdd`: a weighted gradient and bounded
   circulation on strips, `∫∫_strip E = -[∫ v₁ dq]`, force the decay).
3. **Age letters from the vorticity equation** (`TjTrainVort`: `∂_ρE = νΔE - v·∇E` on `tjU`) and
   **the velocity from the vorticity** (`TjTrainKc m`, assembled from `TjTrainBSRep` (`v = K_cE`),
   `TjKcBound`, `TjKcDerivSpace`, `TjKcDerivTime`, `TjWPeriodic`): every word of `v` is `K_c` of
   the same word of `E`, so it is bounded once all suffixes of the word of `E` are weighted.
4. **The induction on the number of age letters** (`TjAbstractInduction`, proved in
   `Assembly.lean` from `TjWPerm`, `TjWLeibniz`, `TjWLinear`): an age letter is moved inside
   (`TjWPerm`), replaced by the right side of the vorticity equation (two more spatial letters, or
   a product `v_j ∂_jE` expanded by Leibniz, `TjWLeibniz`), and the velocity words with the new
   number of age letters follow from step 3.
`trainSTJetsOfBUC_of` (`Assembly.lean`) assembles `TrainSTJetsOfBUC m` from the leaves.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## Vocabulary -/

/-- The closed space-time half-space `[0, ∞) × ℝ²` of the train (`B0140.IsTrain.smooth_v`). -/
abbrev tjU : Set (ℝ × (ℝ × ℝ)) := Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))

/-- The weight `(1 + x₂²)^{(m+1)/2}` of the vorticity clause of `TrainSTJets`. -/
def tjWt (m : ℝ) (x : ℝ × ℝ) : ℝ := (1 + x.2 ^ 2) ^ ((m + 1) / 2)

/-- **Iterated directional derivatives within `[0, ∞) × ℝ²`** along the coordinate directions
`stDir` (`0`: the age `ρ`; `1, 2`: the space variables `q, η`); the head of the word is the
outermost derivative: `tjW (a :: L) h = ∂_a (tjW L h)`. -/
def tjW {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    List (Fin 3) → (ℝ × (ℝ × ℝ) → F) → ℝ × (ℝ × ℝ) → F
  | [], h => h
  | a :: L, h => fun p => fderivWithin ℝ (tjW L h) tjU p (stDir a)

/-- The `2^{|L|}` splittings of a word into two complementary subwords (Leibniz rule). -/
def tjSplits {α : Type*} : List α → List (List α × List α)
  | [] => [([], [])]
  | a :: L => (tjSplits L).map (fun q => (a :: q.1, q.2)) ++
      (tjSplits L).map (fun q => (q.1, a :: q.2))

/-- **The cylinder Biot-Savart velocity of a space-time field, age by age** (SP 2081-2084, `K_c`
including the horizontal mean mode): `tjKc c g (ρ, x) = K_c[g(ρ, ·)](x)`, `Cyl.K` the convolution
over the cell with the periodized kernel `Cyl.bsKernel`. -/
def tjKc (c : ℝ) (g : ℝ × (ℝ × ℝ) → ℝ) (p : ℝ × (ℝ × ℝ)) : UnforcedLeray.Cyl.Vec2 :=
  UnforcedLeray.Cyl.K c (fun y => g (p.1, y)) p.2

/-- Component `j` of the train velocity as a space-time field. -/
abbrev tjV {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (j : Fin 2) :
    ℝ × (ℝ × ℝ) → ℝ :=
  fun p => tr.v p.1 p.2 j

/-- The train vorticity `E = curl v` (`B0238.Ec`) as a space-time field. -/
abbrev tjE {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) : ℝ × (ℝ × ℝ) → ℝ :=
  fun p => UnforcedLeray.B0238.Ec tr p.1 p.2

/-- A space-time field bounded on every `[0, S] × ℝ²`. -/
def TjUBdd (f : ℝ × (ℝ × ℝ) → ℝ) : Prop :=
  ∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, ∀ ρ ∈ Icc (0 : ℝ) S, ∀ x : ℝ × ℝ, |f (ρ, x)| ≤ C

/-- A space-time field bounded on every `[0, S] × ℝ²` with the weight `(1 + x₂²)^{(m+1)/2}`. -/
def TjWBdd (m : ℝ) (f : ℝ × (ℝ × ℝ) → ℝ) : Prop :=
  ∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, ∀ ρ ∈ Icc (0 : ℝ) S, ∀ x : ℝ × ℝ, tjWt m x * |f (ρ, x)| ≤ C

/-! ## Basic facts (proved) -/

theorem uniqueDiffOn_tjU : UniqueDiffOn ℝ tjU :=
  (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ

theorem tjWt_pos (m : ℝ) (x : ℝ × ℝ) : 0 < tjWt m x :=
  Real.rpow_pos_of_pos (by positivity) _

section Words

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

@[simp] theorem tjW_nil (h : ℝ × (ℝ × ℝ) → F) : tjW [] h = h := rfl

theorem tjW_cons (a : Fin 3) (L : List (Fin 3)) (h : ℝ × (ℝ × ℝ) → F) :
    tjW (a :: L) h = fun p => fderivWithin ℝ (tjW L h) tjU p (stDir a) := rfl

theorem tjW_append : ∀ (L₁ L₂ : List (Fin 3)) (h : ℝ × (ℝ × ℝ) → F),
    tjW (L₁ ++ L₂) h = tjW L₁ (tjW L₂ h)
  | [], _, _ => rfl
  | a :: L₁, L₂, h => by
      rw [List.cons_append, tjW_cons, tjW_cons, tjW_append L₁ L₂ h]

/-- Words of fields that agree on `tjU` agree on `tjU`. -/
theorem tjW_congr {f g : ℝ × (ℝ × ℝ) → F} (hfg : EqOn f g tjU) :
    ∀ L : List (Fin 3), EqOn (tjW L f) (tjW L g) tjU
  | [] => hfg
  | a :: L => fun p hp => by
      simp only [tjW_cons]
      rw [fderivWithin_congr (tjW_congr hfg L) (tjW_congr hfg L hp)]

/-- Words of a field `C^∞` on `tjU` are `C^∞` on `tjU`. -/
theorem tjW_contDiffOn {h : ℝ × (ℝ × ℝ) → F} (hh : ContDiffOn ℝ ∞ h tjU) :
    ∀ L : List (Fin 3), ContDiffOn ℝ ∞ (tjW L h) tjU
  | [] => hh
  | a :: L => by
      rw [tjW_cons]
      exact ((contDiffOn_infty_iff_fderivWithin uniqueDiffOn_tjU).1
        (tjW_contDiffOn hh L)).2.clm_apply contDiffOn_const

end Words

/-- The `q`-slice derivative of a field `C^∞` on `tjU` is the word `[1]` (as `PartI.swrLineX`). -/
theorem tjW_one_apply {G : ℝ × (ℝ × ℝ) → ℝ} (hG : ContDiffOn ℝ ∞ G tjU) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (y : ℝ × ℝ) : tjW [1] G (ρ, y) = deriv (fun t : ℝ => G (ρ, (t, y.2))) y.1 := by
  have hp : ((ρ, y) : ℝ × (ℝ × ℝ)) ∈ tjU := ⟨mem_Ici.2 hρ, mem_univ y⟩
  have hd : DifferentiableWithinAt ℝ G tjU (ρ, y) := (hG.differentiableOn (by simp)) _ hp
  have hγ : HasDerivAt (fun t : ℝ => ((ρ, (t, y.2)) : ℝ × (ℝ × ℝ))) ((0, (1, 0)) : ℝ × (ℝ × ℝ))
      y.1 := (hasDerivAt_const _ _).prodMk ((hasDerivAt_id _).prodMk (hasDerivAt_const _ _))
  have hmaps : MapsTo (fun t : ℝ => ((ρ, (t, y.2)) : ℝ × (ℝ × ℝ))) univ tjU :=
    fun _ _ => ⟨mem_Ici.2 hρ, mem_univ _⟩
  have h := hd.hasFDerivWithinAt.comp_hasDerivWithinAt y.1 hγ.hasDerivWithinAt hmaps
  exact ((hasDerivWithinAt_univ.1 h).deriv).symm

/-- The `η`-slice derivative of a field `C^∞` on `tjU` is the word `[2]` (as `PartI.swrLineY`). -/
theorem tjW_two_apply {G : ℝ × (ℝ × ℝ) → ℝ} (hG : ContDiffOn ℝ ∞ G tjU) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (y : ℝ × ℝ) : tjW [2] G (ρ, y) = deriv (fun t : ℝ => G (ρ, (y.1, t))) y.2 := by
  have hp : ((ρ, y) : ℝ × (ℝ × ℝ)) ∈ tjU := ⟨mem_Ici.2 hρ, mem_univ y⟩
  have hd : DifferentiableWithinAt ℝ G tjU (ρ, y) := (hG.differentiableOn (by simp)) _ hp
  have hγ : HasDerivAt (fun t : ℝ => ((ρ, (y.1, t)) : ℝ × (ℝ × ℝ))) ((0, (0, 1)) : ℝ × (ℝ × ℝ))
      y.2 := (hasDerivAt_const _ _).prodMk ((hasDerivAt_const _ _).prodMk (hasDerivAt_id _))
  have hmaps : MapsTo (fun t : ℝ => ((ρ, (y.1, t)) : ℝ × (ℝ × ℝ))) univ tjU :=
    fun _ _ => ⟨mem_Ici.2 hρ, mem_univ _⟩
  have h := hd.hasFDerivWithinAt.comp_hasDerivWithinAt y.2 hγ.hasDerivWithinAt hmaps
  exact ((hasDerivWithinAt_univ.1 h).deriv).symm

/-- The splittings of a word share out its letters. -/
theorem tjSplits_count {α : Type*} [DecidableEq α] (b : α) :
    ∀ (L : List α), ∀ s ∈ tjSplits L, s.1.count b + s.2.count b = L.count b
  | [] => by simp [tjSplits]
  | a :: L => by
      intro s hs
      simp only [tjSplits, List.mem_append, List.mem_map] at hs
      rcases hs with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      · have := tjSplits_count b L q hq
        simp only [List.count_cons]
        omega
      · have := tjSplits_count b L q hq
        simp only [List.count_cons]
        omega

/-! ## Leaves: calculus of words (manuscript-independent) -/

/-- **The jet norm by the coordinate words** (calculus): for a field `C^∞` on `tjU` and `p ∈ tjU`,
`‖D^n h(p)‖ ≤ K Σ_{L : Fin n → Fin 3} ‖tjW L h p‖` (`D^n` within `tjU`). (Induction with
`iteratedFDerivWithin_succ_apply_left`, `fderivWithin_congr` on `tjU` and the derivative of the
evaluation at fixed vectors: `tjW (List.ofFn L) h p = iteratedFDerivWithin ℝ n h tjU p (stDir ∘ L)`;
then expand every argument in the basis `stDir` (coordinates bounded by the sup norm of
`ℝ × (ℝ × ℝ)`) by multilinearity, `ContinuousMultilinearMap.opNorm_le_bound`. `K = 1` works.) -/
def TjJetNorm : Prop :=
  ∀ n : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (h : ℝ × (ℝ × ℝ) → F), ContDiffOn ℝ ∞ h tjU → ∀ p ∈ tjU,
      ‖iteratedFDerivWithin ℝ n h tjU p‖ ≤ K * ∑ L : Fin n → Fin 3, ‖tjW (List.ofFn L) h p‖

/-- **Words do not depend on the order of their letters** (symmetry of mixed derivatives within
`tjU`; `tjU` is the closure of its interior `Ioi 0 ×ˢ univ`). (Induction on `List.Perm`: `cons` by
`fderivWithin_congr`; `swap` by `ContDiffWithinAt.isSymmSndFDerivWithinAt` for `tjW L h` and the
derivative of `q ↦ fderivWithin g tjU q v`; `trans`.) -/
def TjWPerm : Prop :=
  ∀ h : ℝ × (ℝ × ℝ) → ℝ, ContDiffOn ℝ ∞ h tjU → ∀ L L' : List (Fin 3), L.Perm L' →
    ∀ p ∈ tjU, tjW L h p = tjW L' h p

/-- **The Leibniz rule for words** (calculus): `∂_L(fg) = Σ_{splittings (L₁, L₂) of L} ∂_{L₁}f ∂_{L₂}g`
on `tjU`, for `f, g` `C^∞` on `tjU`. (Induction on `L`: `fderivWithin_mul`, `fderivWithin_sum` /
induction on the list sum, `fderivWithin_congr` with the inductive identity on `tjU`.) -/
def TjWLeibniz : Prop :=
  ∀ f g : ℝ × (ℝ × ℝ) → ℝ, ContDiffOn ℝ ∞ f tjU → ContDiffOn ℝ ∞ g tjU →
    ∀ L : List (Fin 3), ∀ p ∈ tjU,
      tjW L (fun q => f q * g q) p = ((tjSplits L).map (fun s => tjW s.1 f p * tjW s.2 g p)).sum

/-- **Words are linear and commute with components** (calculus): on `tjU`, for fields `C^∞` on
`tjU`, `tjW L (f + g) = tjW L f + tjW L g`, `tjW L (f - g) = tjW L f - tjW L g`,
`tjW L (r f) = r tjW L f`, and `tjW L (h · j) = (tjW L h) j` for a vector field `h`. (Induction on
`L` with `fderivWithin_add`, `fderivWithin_sub`, `fderivWithin_const_mul`, and
`(EuclideanSpace.proj j).fderivWithin_comp` / `fderivWithin_clm_apply`; `tjW_congr` on `tjU`.) -/
def TjWLinear : Prop :=
  (∀ f g : ℝ × (ℝ × ℝ) → ℝ, ContDiffOn ℝ ∞ f tjU → ContDiffOn ℝ ∞ g tjU →
    ∀ L : List (Fin 3), ∀ p ∈ tjU, tjW L (fun q => f q + g q) p = tjW L f p + tjW L g p) ∧
  (∀ f g : ℝ × (ℝ × ℝ) → ℝ, ContDiffOn ℝ ∞ f tjU → ContDiffOn ℝ ∞ g tjU →
    ∀ L : List (Fin 3), ∀ p ∈ tjU, tjW L (fun q => f q - g q) p = tjW L f p - tjW L g p) ∧
  (∀ (r : ℝ) (f : ℝ × (ℝ × ℝ) → ℝ), ContDiffOn ℝ ∞ f tjU →
    ∀ L : List (Fin 3), ∀ p ∈ tjU, tjW L (fun q => r * f q) p = r * tjW L f p) ∧
  (∀ h : ℝ × (ℝ × ℝ) → UnforcedLeray.Cyl.Vec2, ContDiffOn ℝ ∞ h tjU → ∀ (j : Fin 2)
    (L : List (Fin 3)), ∀ p ∈ tjU, tjW L (fun q => h q j) p = tjW L h p j)

/-- **Spatial words are slice derivatives** (calculus): for a field `C^∞` on `tjU` and a word with
no age letter, `|tjW L h (ρ, x)| ≤ ‖D^{|L|}[h(ρ, ·)](x)‖`. (The line `y ↦ (ρ, y)` stays in `tjU`, so
`tjW L h (ρ, x) = iteratedFDeriv ℝ |L| (h(ρ, ·)) x (i ↦ (stDir (L i)).2)` by induction, the
`HasFDerivWithinAt.comp` with the embedding as in `PartI.swrLineX`; the directions have norm `1`.) -/
def TjSliceNorm : Prop :=
  ∀ h : ℝ × (ℝ × ℝ) → ℝ, ContDiffOn ℝ ∞ h tjU → ∀ L : List (Fin 3), 0 ∉ L →
    ∀ ρ : ℝ, 0 ≤ ρ → ∀ x : ℝ × ℝ,
      |tjW L h (ρ, x)| ≤ ‖iteratedFDeriv ℝ L.length (fun y => h (ρ, y)) x‖

/-- **Spatial lines** (calculus): for a field `C^∞` on `tjU`, a spatial direction `a ≠ 0` and
`p ∈ tjU`, the restriction `t ↦ h(p + t·stDir a)` is `C^∞` and its derivatives are the words
`a^j`: `iteratedDeriv j (t ↦ h(p + t·e_a)) t = tjW (a^j) h (p + t·e_a)` (the line stays in `tjU`;
induction on `j` with `iteratedDeriv_succ'` and the chain rule within `tjU`). -/
def TjLineDeriv : Prop :=
  ∀ h : ℝ × (ℝ × ℝ) → ℝ, ContDiffOn ℝ ∞ h tjU → ∀ a : Fin 3, a ≠ 0 → ∀ p ∈ tjU,
    ContDiff ℝ ∞ (fun t : ℝ => h (p + t • stDir a)) ∧
    ∀ (j : ℕ) (t : ℝ), iteratedDeriv j (fun t : ℝ => h (p + t • stDir a)) t =
      tjW (List.replicate j a) h (p + t • stDir a)

/-- **Local interpolation on a unit interval** (Landau-Kolmogorov; calculus): for `N ≥ 1` there is
`K` with `|g'(t₀)| ≤ K (A^{1-1/N} M^{1/N} + A)` whenever `|g| ≤ A` and `|g^{(N)}| ≤ M` on
`[t₀, t₀ + 1]`. (For `N ≥ 2`: Taylor at the nodes `t₀ + ih`, `0 ≤ i < N`, `0 < h ≤ 1/N`, with the
Lagrange remainder `|R_i| ≤ M (ih)^N / N!` (`taylor_mean_remainder_lagrange`); weights `a_i` with
`Σ_i a_i i^j = δ_{j1}`, `j < N` (the Vandermonde matrix of the nodes `0, …, N-1` is invertible,
`Matrix.det_vandermonde_ne_zero_iff`) give `h g'(t₀) = Σ a_i g(t₀ + ih) - Σ a_i R_i`, so
`|g'(t₀)| ≤ C (A/h + M h^{N-1})`; take `h = min (1/N) ((A/M)^{1/N})`.) -/
def Interp1D : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∃ K : ℝ, 0 ≤ K ∧ ∀ (g : ℝ → ℝ) (t₀ A M : ℝ), ContDiff ℝ N g →
    (∀ t ∈ Icc t₀ (t₀ + 1), |g t| ≤ A) → (∀ t ∈ Icc t₀ (t₀ + 1), |iteratedDeriv N g t| ≤ M) →
    |deriv g t₀| ≤ K * (A ^ (1 - 1 / (N : ℝ)) * M ^ (1 / (N : ℝ)) + A)

/-- **The finite-difference estimate** (calculus; the first half of `Interp1D`): for `N ≥ 2` there is
`W` with `|g'(t₀)| ≤ W (A/h + M h^{N-1})` for every `0 < h ≤ 1/N`, whenever `|g| ≤ A` and
`|g^{(N)}| ≤ M` on `[t₀, t₀ + 1]`. (Taylor at the nodes `t₀ + ih`, `i < N`, with the Lagrange
remainders `|R_i| ≤ M (ih)^N / N!`; weights `w_i` with `Σ_i w_i i^j = δ_{j1}` for `j < N` from the
invertible Vandermonde matrix of the nodes `0, …, N - 1`; `h g'(t₀) = Σ_i w_i g(t₀ + ih) -
Σ_i w_i R_i`.) -/
def Interp1DFD : Prop :=
  ∀ N : ℕ, 2 ≤ N → ∃ W : ℝ, 0 ≤ W ∧ ∀ (g : ℝ → ℝ) (t₀ A M : ℝ), ContDiff ℝ N g →
    (∀ t ∈ Icc t₀ (t₀ + 1), |g t| ≤ A) → (∀ t ∈ Icc t₀ (t₀ + 1), |iteratedDeriv N g t| ≤ M) →
    ∀ h : ℝ, 0 < h → h ≤ 1 / (N : ℝ) → |deriv g t₀| ≤ W * (A / h + M * h ^ (N - 1))

/-- **Weighted interpolation along spatial words** (calculus; the interpolation of SP 2869-2870,
"interpolating its Gaussian-small unweighted norm with a larger fixed weighted norm"): if
`(1 + x₂²)^{β/2}|h| ≤ A` and every spatial word of `h` is bounded on `[0, S] × ℝ²`, then every spatial
word of `h` is bounded with the weight `(1 + x₂²)^{γ/2}`, for every `0 ≤ γ < β`. (Induction on the
word, one letter at a time: `Interp1D` with `N` large along the line of the letter (`TjLineDeriv`)
turns the weight `γ''` of the inner word into `γ''(1 - 1/N) ≥ γ'`; on a unit segment
`1 + y₂² ≥ (1 + x₂²)/5`.) -/
def TjSpatialInterp : Prop :=
  ∀ (β γ : ℝ), 0 ≤ γ → γ < β → ∀ h : ℝ × (ℝ × ℝ) → ℝ, ContDiffOn ℝ ∞ h tjU →
    ∀ S : ℝ, 0 ≤ S →
    (∃ A : ℝ, ∀ ρ ∈ Icc (0 : ℝ) S, ∀ x : ℝ × ℝ, (1 + x.2 ^ 2) ^ (β / 2) * |h (ρ, x)| ≤ A) →
    (∀ L : List (Fin 3), 0 ∉ L → ∃ M : ℝ, ∀ ρ ∈ Icc (0 : ℝ) S, ∀ x : ℝ × ℝ,
      |tjW L h (ρ, x)| ≤ M) →
    ∀ L : List (Fin 3), 0 ∉ L → ∃ C : ℝ, ∀ ρ ∈ Icc (0 : ℝ) S, ∀ x : ℝ × ℝ,
      (1 + x.2 ^ 2) ^ (γ / 2) * |tjW L h (ρ, x)| ≤ C

/-- **Decay of a periodic field from its weighted gradient and bounded strip integrals** (calculus;
the mechanism of SP 270-288: an `L¹` vorticity with bounded circulation on strips cannot tend to a
nonzero constant): for `β > 1`, `c > 0` there is `K` such that a `C¹` field `E` on the plane,
`c`-periodic in `q`, with `(1 + η²)^{β/2}|∂_qE|, (1 + η²)^{β/2}|∂_ηE| ≤ A` and with all the strip
integrals `∫_a^b ∫_{-c/2}^{c/2} E dq dη` bounded, satisfies `(1 + η²)^{(β-1)/2}|E| ≤ K A`. (The
horizontal mean `Ē(η)` obeys `|E(q, η) - Ē(η)| ≤ c A (1 + η²)^{-β/2}` (reduce `q` to the cell by
periodicity) and `|Ē(R) - Ē(η)| ≤ A T(η)`, `T(η) = ∫_{|s| ≥ |η|} (1 + s²)^{-β/2} ds ≤
K₀(1 + η²)^{-(β-1)/2}`; if `|Ē(η₀)| > 2A T(η₀)` for some `η₀ ≥ 0`, then `Ē` keeps its sign and stays
above `δ > 0` on `[η₀, ∞)`, so `∫_{η₀}^R c Ē → ∞`, contradicting the bounded strip integrals;
symmetrically for `η₀ ≤ 0`; `K = 2K₀ + c`.) -/
def TjDecayOfGrad : Prop :=
  ∀ (β c : ℝ), 1 < β → 0 < c → ∃ K : ℝ, 0 ≤ K ∧ ∀ (E : ℝ × ℝ → ℝ) (A B : ℝ), ContDiff ℝ 1 E →
    (∀ x : ℝ × ℝ, E (x.1 + c, x.2) = E x) →
    (∀ x : ℝ × ℝ, (1 + x.2 ^ 2) ^ (β / 2) * |UnforcedLeray.Cyl.partialQ E x| ≤ A) →
    (∀ x : ℝ × ℝ, (1 + x.2 ^ 2) ^ (β / 2) * |UnforcedLeray.Cyl.partialEta E x| ≤ A) →
    (∀ a b : ℝ, |∫ η in a..b, ∫ q in (-(c / 2))..(c / 2), E (q, η)| ≤ B) →
    ∀ x : ℝ × ℝ, (1 + x.2 ^ 2) ^ ((β - 1) / 2) * |E x| ≤ K * A

/-- **Words of a periodic field are periodic** (calculus: the translation `(ρ, q, η) ↦
(ρ, q + c, η)` preserves `tjU` and the directions; `fderivWithin` of `h ∘ T` on `tjU`, induction on
`L`). -/
def TjWPeriodic : Prop :=
  ∀ (c : ℝ) (h : ℝ × (ℝ × ℝ) → ℝ), ContDiffOn ℝ ∞ h tjU →
    (∀ ρ : ℝ, 0 ≤ ρ → ∀ x : ℝ × ℝ, h (ρ, (x.1 + c, x.2)) = h (ρ, x)) →
    ∀ L : List (Fin 3), ∀ ρ : ℝ, 0 ≤ ρ → ∀ x : ℝ × ℝ,
      tjW L h (ρ, (x.1 + c, x.2)) = tjW L h (ρ, x)

/-- **The induction on the number of age letters** (calculus; the vorticity equation trades an age
derivative for spatial ones, SP 270-288, 438-461): let `E, V₀, V₁` be `C^∞` on `tjU` with
`∂_ρE = ν(∂_q²E + ∂_η²E) - (V₀ ∂_qE + V₁ ∂_ηE)` on `tjU`; if every word with no age letter is bounded
(weighted for `E`), and every word of `V_j` is bounded as soon as all suffixes of the same word of
`E` are weighted-bounded (the Biot-Savart law), then every word is bounded (weighted for `E`).
Proved in `Assembly.lean` (`tjAbstractInduction_of`) from `TjWPerm`, `TjWLeibniz`, `TjWLinear`. -/
def TjAbstractInduction : Prop :=
  ∀ (m ν : ℝ) (E V₀ V₁ : ℝ × (ℝ × ℝ) → ℝ),
    ContDiffOn ℝ ∞ E tjU → ContDiffOn ℝ ∞ V₀ tjU → ContDiffOn ℝ ∞ V₁ tjU →
    (∀ p ∈ tjU, tjW [0] E p = ν * (tjW [1, 1] E p + tjW [2, 2] E p) -
        (V₀ p * tjW [1] E p + V₁ p * tjW [2] E p)) →
    (∀ L : List (Fin 3), 0 ∉ L → TjWBdd m (tjW L E) ∧ TjUBdd (tjW L V₀) ∧ TjUBdd (tjW L V₁)) →
    (∀ L : List (Fin 3), (∀ L' : List (Fin 3), L' <:+ L → TjWBdd m (tjW L' E)) →
        TjUBdd (tjW L V₀) ∧ TjUBdd (tjW L V₁)) →
    ∀ L : List (Fin 3), TjWBdd m (tjW L E) ∧ TjUBdd (tjW L V₀) ∧ TjUBdd (tjW L V₁)

/-! ## Leaves: the cylinder Biot-Savart operator (manuscript-independent) -/

/-- **`K_c` of a weighted field is bounded** (SP 2081-2084, 3052-3058; `Cyl.bsKernel_split`: on the
cell `K_c = k_near + k_far`, `∫_cell |k_near| ≤ C`, `|k_far| ≤ 2`, uniformly for `c ≥ 1`): for `g`
continuous on `tjU`, `c`-periodic in `q`, with `(1 + x₂²)^{(m+1)/2}|g| ≤ A` on `[0, S] × ℝ²`
(`m > 0`), `‖K_c[g(ρ, ·)](x)‖ ≤ A C + 2Ac ∫_ℝ (1 + s²)^{-(m+1)/2} ds` on `[0, S] × ℝ²`. (Centred
form `Cyl.K_eq_reflect`, `∫_cell |g(ρ, x - y)| ≤ A ∫_cell (1 + (x₂ - y₂)²)^{-(m+1)/2} dy`.) -/
def TjKcBound : Prop :=
  ∀ (c m : ℝ), 1 ≤ c → 0 < m → ∀ g : ℝ × (ℝ × ℝ) → ℝ, ContinuousOn g tjU →
    (∀ ρ : ℝ, 0 ≤ ρ → ∀ x : ℝ × ℝ, g (ρ, (x.1 + c, x.2)) = g (ρ, x)) →
    TjWBdd m g → ∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, ∀ ρ ∈ Icc (0 : ℝ) S, ∀ x : ℝ × ℝ,
      ‖tjKc c g (ρ, x)‖ ≤ C

/-- **Spatial derivatives pass under `K_c`** (measure theory): if `h` is `C^∞` on `tjU` and equals
`K_c g` on `tjU`, `g` `C^∞` on `tjU`, `c`-periodic, with `g` and `∂_a g` weighted-bounded (`a = 1, 2`),
then `∂_a h = K_c(∂_a g)` on `tjU`. (`∂_a h(p)` is the derivative of `t ↦ h(p + t e_a)`, the line
stays in `tjU` (`TjLineDeriv`-type chain rule); in the centred form `Cyl.K_eq_reflect` differentiate
`t ↦ ∫_cell g(ρ, x + t e_a - y) K_c(y) dy` under the integral,
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`, dominated by
`A (1 + (x₂ - y₂)²)^{-(m+1)/2}·5^{(m+1)/2}‖K_c(y)‖`, integrable by `Cyl.bsKernel_split`.) -/
def TjKcDerivSpace : Prop :=
  ∀ (c m : ℝ), 1 ≤ c → 0 < m → ∀ (g : ℝ × (ℝ × ℝ) → ℝ) (h : ℝ × (ℝ × ℝ) → UnforcedLeray.Cyl.Vec2),
    ContDiffOn ℝ ∞ g tjU → ContDiffOn ℝ ∞ h tjU →
    (∀ ρ : ℝ, 0 ≤ ρ → ∀ x : ℝ × ℝ, g (ρ, (x.1 + c, x.2)) = g (ρ, x)) →
    TjWBdd m g → ∀ a : Fin 3, a ≠ 0 → TjWBdd m (tjW [a] g) →
    EqOn h (tjKc c g) tjU → EqOn (tjW [a] h) (tjKc c (tjW [a] g)) tjU

/-- **The age derivative passes under `K_c`** (measure theory): as `TjKcDerivSpace` for the age
direction `0`. (At `ρ > 0`: `∂_ρ h(ρ, x) = d/dt h(t, x)` at `t = ρ` (interior point), and
`d/dt ∫_cell g(t, y) K_c(x - y) dy = ∫_cell ∂_t g(t, y) K_c(x - y) dy` by
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` with the weighted bound of `∂_ρ g` on
`[ρ/2, ρ + 1]`; at `ρ = 0`: both sides are continuous on `tjU` (`h` is `C^∞`; `K_c` of a continuous
weighted-bounded field is continuous by dominated convergence) and agree for `ρ > 0`.) -/
def TjKcDerivTime : Prop :=
  ∀ (c m : ℝ), 1 ≤ c → 0 < m → ∀ (g : ℝ × (ℝ × ℝ) → ℝ) (h : ℝ × (ℝ × ℝ) → UnforcedLeray.Cyl.Vec2),
    ContDiffOn ℝ ∞ g tjU → ContDiffOn ℝ ∞ h tjU →
    (∀ ρ : ℝ, 0 ≤ ρ → ∀ x : ℝ × ℝ, g (ρ, (x.1 + c, x.2)) = g (ρ, x)) →
    TjWBdd m g → TjWBdd m (tjW [0] g) →
    EqOn h (tjKc c g) tjU → EqOn (tjW [0] h) (tjKc c (tjW [0] g)) tjU

/-! ## Leaves: the train -/

/-- **The vorticity of the train on `[0, ∞) × ℝ²`** (SP 270-288, 2081-2084; `B0238.Ec`): `E` is
`C^∞` on `tjU`, `E = ∂_q v₂ - ∂_η v₁` there (`Cyl.curl` of the slice; the slice partials are the words
`[1]`, `[2]`, as in `PartI.swrLineX`, `PartI.swrLineY`), and it solves the vorticity equation
`∂_ρE = ν(∂_q²E + ∂_η²E) - (v₁∂_qE + v₂∂_ηE)` on `tjU`: for `ρ > 0` this is
`B0238.Ec_vorticity_equation` (the word `[0]` is `deriv (t ↦ E(t, x)) ρ` at an interior point, `[1, 1]`
is `Cyl.partialQ (Cyl.partialQ (Ec tr ρ))`, ...); at `ρ = 0` both sides are continuous on `tjU` and
agree for `ρ > 0`. -/
def TjTrainVort : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c),
    ContDiffOn ℝ ∞ (tjE tr) tjU ∧
    (∀ p ∈ tjU, tjE tr p = tjW [1] (tjV tr 1) p - tjW [2] (tjV tr 0) p) ∧
    ∀ p ∈ tjU, tjW [0] (tjE tr) p = ν * (tjW [1, 1] (tjE tr) p + tjW [2, 2] (tjE tr) p) -
        (tjV tr 0 p * tjW [1] (tjE tr) p + tjV tr 1 p * tjW [2] (tjE tr) p)

/-- **The weighted gradient of the vorticity on the plane** (SP 270-288, 2866-2873; `LadTrainBdd`
on the cell, extended by periodicity): `(1 + x₂²)^{(m+2)/2}|∂_aE| ≤ A` on `[0, S] × ℝ²`, `a = 1, 2`.
(`tjW [a] (tjE tr) (ρ, x) = B0579.pd (a - 1) (Ec tr ρ) x`; reduce `x` to the cell by `q ↦ q - kc`
(`Ec tr ρ` is `c`-periodic, `PartI.vjl_curl_periodic`); on the cell `B0579.jb x ≥ 1 + x₂²`.) -/
def TjLadGrad (m : ℝ) : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c), 0 < c →
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    ∀ a : Fin 3, a ≠ 0 → ∀ S : ℝ, 0 ≤ S → ∃ A : ℝ, ∀ ρ ∈ Icc (0 : ℝ) S, ∀ x : ℝ × ℝ,
      (1 + x.2 ^ 2) ^ ((m + 2) / 2) * |tjW [a] (tjE tr) (ρ, x)| ≤ A

/-- **The circulation of the train on strips** (SP 270-288: the scalar vorticity, zero circulation
on the cylinder): for `c > 0`, every age `ρ ≥ 0` and `‖v(ρ)‖ ≤ M`,
`|∫_a^b ∫_{-c/2}^{c/2} E(ρ, q, η) dq dη| ≤ 2cM`. (`E = ∂_q v₂ - ∂_η v₁` (`Cyl.curl`); the `∂_q v₂`
part integrates to `v₂(c/2, η) - v₂(-c/2, η) = 0` (`IsTrain.periodic_v`); after Fubini on the
rectangle (`intervalIntegral_integral_swap` or `MeasureTheory.integral_prod`, the integrand is
continuous) the `∂_η v₁` part is `∫_{-c/2}^{c/2} (v₁(q, b) - v₁(q, a)) dq`
(`intervalIntegral.integral_deriv_eq_sub`), bounded by `2cM`.) -/
def TjCirculationBdd : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c), 0 < c → ∀ ρ : ℝ, 0 ≤ ρ → ∀ M : ℝ,
    (∀ x : ℝ × ℝ, ‖tr.v ρ x‖ ≤ M) →
    ∀ a b : ℝ, |∫ η in a..b, ∫ q in (-(c / 2))..(c / 2), UnforcedLeray.B0238.Ec tr ρ (q, η)| ≤
      2 * c * M

/-- **The Biot-Savart law of the train** (SP 261-266 `v = ∇^⊥ψ` with decaying stream; SP 2081-2084,
`K_c` with the horizontal mean mode; SP 286-288, `v(-x) = -v(x)`): for `0 < ν ≤ 1`, `c = ν⁻²`, a
`BUC` train with the bounds `LadTrainBdd` satisfies `v(ρ) = K_c E(ρ)` pointwise on `[0, ∞) × ℝ²`.
(`w = v(ρ) - K_cE(ρ)` is bounded, `C¹`, `c`-periodic, divergence- and curl-free, hence constant
(`w₁ - iw₂` is entire and bounded); it is odd (`v` odd, `E` even, the kernel odd), hence `0`. The
divergence and curl of `K_cE(ρ)` need the decay of `E` and `∇E`: `TjVortDecay`, `TjLadGrad`.)
Designed by the organize task `PartIII-a:T21/2/7/2/1/1/2/10/org`. -/
def TjTrainBSRep (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    UnforcedLeray.Short.PartI.IsBUCTrain tr →
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    ∀ p ∈ tjU, tr.v p.1 p.2 = tjKc (ν ^ (-2 : ℝ)) (tjE tr) p

/-! ## Intermediate statements (proved in `Assembly.lean`) -/

/-- **The vorticity decays** (SP 270-288: zero circulation, `L¹` vorticity): for a `BUC` train with
the bounds `LadTrainBdd`, `(1 + x₂²)^{(m+1)/2}|E| ≤ C` on `[0, S] × ℝ²` (`tjVortDecay_of`: from
`TjDecayOfGrad` with `β = m + 2`, the weighted gradient `TjLadGrad`, and the strip circulation
`TjCirculationBdd` with `M = sup |v|`). -/
def TjVortDecay (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    UnforcedLeray.Short.PartI.IsBUCTrain tr →
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) → TjWBdd m (tjE tr)

/-- **The words with no age letter** (`IsBUCTrain`, interpolation, decay): every spatial word of `E`
is weighted-bounded, every spatial word of `v_j` bounded. -/
def TjTrainSpace (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    UnforcedLeray.Short.PartI.IsBUCTrain tr →
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    ∀ L : List (Fin 3), 0 ∉ L →
      TjWBdd m (tjW L (tjE tr)) ∧ TjUBdd (tjW L (tjV tr 0)) ∧ TjUBdd (tjW L (tjV tr 1))

/-- **The velocity words from the vorticity words** (the Biot-Savart law): a word of `v_j` is
bounded as soon as every suffix of the same word of `E` is weighted-bounded. -/
def TjTrainKc (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    UnforcedLeray.Short.PartI.IsBUCTrain tr →
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    ∀ L : List (Fin 3), (∀ L' : List (Fin 3), L' <:+ L → TjWBdd m (tjW L' (tjE tr))) →
      TjUBdd (tjW L (tjV tr 0)) ∧ TjUBdd (tjW L (tjV tr 1))

end UnforcedLeray.Short.IIIa
