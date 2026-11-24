import UnforcedLeray.Short.PartI.Sub.PartI_T08_7
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ForcingIBP
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.TransportBound.Split

/-!
# Part I, task `PartI:T08/7/2` (`JTLin`) and `PartI:T08/7/3` (`JTQuad`): decomposition

Source: `the November 2 reference manuscript` lines 352-358 (differentiated
transport `‖[D^j, e·∇]e‖₂ ≤ C_j ‖∇e‖_∞ ‖D^j e‖₂`, period-independent constants).

The bilinear transport `advB u h = (u·∇)h` is introduced with explicit components, so that
`Train.advection f = advB f f` and `linTerm V f = advB V f + advB f V` (proved here). The leaves are

* `JTAdvInt` (integrability of the pairing integrand, shared),
* `JTBoundA` (`⟨D^j f, D^j (V·∇)f⟩`, uses `div V = 0` for the top term),
* `JTBoundB` (`⟨D^j f, D^j (f·∇)V⟩`),
* `JTBoundQ` (`⟨D^j f, D^j (f·∇)f⟩`, uses the period-independent Gagliardo-Nirenberg `CylGN`),

and `jtLin_of`, `jtQuad_of` assemble `JTLin`, `JTQuad` from them (smoothness proved here).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec toVec)

/-- The derivative letter of the coordinate `m`: `true` is `∂_q` (component `0`), `false` is `∂_η`. -/
def dirOf (m : Fin 2) : Bool := decide (m = 0)

/-- `k`-th component of `(u·∇)h`: `∑_m u_m ∂_m h_k`. -/
def advTerm (u h : Plane → Vec) (k : Fin 2) (z : Plane) : ℝ :=
  ∑ m : Fin 2, u z m * wordComp [dirOf m] h k z

/-- The bilinear transport `(u·∇)h`. -/
def advB (u h : Plane → Vec) : Plane → Vec :=
  fun z => toVec (advTerm u h 0 z, advTerm u h 1 z)

theorem advB_apply (u h : Plane → Vec) (k : Fin 2) (z : Plane) : advB u h z k = advTerm u h k z := by
  fin_cases k <;> rfl

theorem advection_eq_advB (f : Plane → Vec) : Train.advection f = advB f f := by
  funext z
  ext k
  rw [advB_apply]
  fin_cases k <;>
    simp [Train.advection, advTerm, wordComp, dirOf, Fin.sum_univ_two, B0151.derivWord] <;> rfl

theorem contDiff_coord (k : Fin 2) : ContDiff ℝ ∞ (fun v : Vec => v k) :=
  (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff

theorem contDiff_comp_coord {g : Plane → Vec} (hg : ContDiff ℝ ∞ g) (k : Fin 2) :
    ContDiff ℝ ∞ (fun x => g x k) := (contDiff_coord k).comp hg

theorem contDiff_wordComp {h : Plane → Vec} (hh : ContDiff ℝ ∞ h) (w : List Bool) (k : Fin 2) :
    ContDiff ℝ ∞ (wordComp w h k) := by
  have h1 : ContDiff ℝ ∞ (fun x => h x k) := contDiff_comp_coord hh k
  exact B0151.contDiff_derivWord h1 w

theorem contDiff_advB {u h : Plane → Vec} (hu : ContDiff ℝ ∞ u) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (advB u h) := by
  have hc : ∀ k : Fin 2, ContDiff ℝ ∞ (fun z => advTerm u h k z) := by
    intro k
    unfold advTerm
    refine ContDiff.sum fun m _ => ?_
    exact (contDiff_comp_coord hu m).mul (contDiff_wordComp hh _ k)
  have : advB u h = Train.toVecL ∘ (fun z => (advTerm u h 0 z, advTerm u h 1 z)) := rfl
  rw [this]
  exact Train.toVecL.contDiff.comp ((hc 0).prodMk (hc 1))

theorem wordComp_add {g₁ g₂ : Plane → Vec} (h₁ : ContDiff ℝ ∞ g₁) (h₂ : ContDiff ℝ ∞ g₂)
    (w : List Bool) (k : Fin 2) (z : Plane) :
    wordComp w (fun x => g₁ x + g₂ x) k z = wordComp w g₁ k z + wordComp w g₂ k z := by
  have h := ForcingIBP.derivWord_add_smooth w (fun x => g₁ x k) (fun x => g₂ x k)
    (contDiff_comp_coord h₁ k) (contDiff_comp_coord h₂ k)
  unfold wordComp
  have e : (fun x => (g₁ x + g₂ x) k) = fun x => g₁ x k + g₂ x k := rfl
  rw [e, h]

theorem jetInt_add {c : ℝ} {j : ℕ} {f g₁ g₂ : Plane → Vec} (h₁ : ContDiff ℝ ∞ g₁)
    (h₂ : ContDiff ℝ ∞ g₂) (I₁ : JetInt c j f g₁) (I₂ : JetInt c j f g₂) :
    JetInt c j f (fun z => g₁ z + g₂ z) := by
  unfold JetInt at *
  have key : (fun z => ∑ w ∈ wordsOfLength j, ∑ k : Fin 2,
        wordComp w f k z * wordComp w (fun x => g₁ x + g₂ x) k z) =
      fun z => (∑ w ∈ wordsOfLength j, ∑ k : Fin 2, wordComp w f k z * wordComp w g₁ k z) +
        (∑ w ∈ wordsOfLength j, ∑ k : Fin 2, wordComp w f k z * wordComp w g₂ k z) := by
    funext z
    simp only [wordComp_add h₁ h₂, mul_add, Finset.sum_add_distrib]
  rw [key]
  exact I₁.add I₂

theorem linTerm_eq {V f : Plane → Vec} (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f) :
    linTerm V f = fun z => advB V f z + advB f V z := by
  funext z
  ext k
  simp only [linTerm, advection_eq_advB, PiLp.sub_apply, PiLp.add_apply, advB_apply, advTerm,
    Fin.sum_univ_two, wordComp_add hV hf]
  ring

/-- **Leaf (integrability of the pairing integrand)** (lines 352-358): if `u, h` are smooth with all
words bounded, one of them (and `f`) has all words in `L²(cell)`, then `∂_w (u·∇)h` is a finite sum of
products (bounded word)*(L² word), hence in L², and the integrand of `⟨D^j f, D^j (u·∇)h⟩`
on the cell is integrable. Route: Leibniz for `derivWord` of a product over subsets of the word
(induction on the word; `Lib/TrainB/SmoothProduct.lean`, `derivWord_comm`) shows `∂_w (u·∇)h` is a
finite sum of products of bounded continuous words; `MemLp.integrable_mul`. -/
def JTAdvInt : Prop :=
  ∀ (j : ℕ) (c : ℝ) (u h f : Plane → Vec), ContDiff ℝ ∞ u → ContDiff ℝ ∞ h → CellSmoothL2 c f →
    (CellSmoothL2 c u ∨ CellSmoothL2 c h) →
    (∀ (w : List Bool) (k : Fin 2), ∃ M : ℝ, ∀ z : Plane, |wordComp w u k z| ≤ M) →
    (∀ (w : List Bool) (k : Fin 2), ∃ M : ℝ, ∀ z : Plane, |wordComp w h k z| ≤ M) →
    JetInt c j f (advB u h)

/-- **Leaf (cross term `(V·∇)f`)** (lines 352-358): Leibniz over `≤ 2^j` splittings of the word;
the top term `(V·∇)D^j f` pairs to `0` with `D^j f` since `div V = 0` (integration by parts,
`ViscousIBP.lean` `word_ibp`, periodicity `Cyl.IsPeriodic`); the others are `d_S V · d_{∂_m w∖S} f`
with `|S| = i ∈ [1,j]`, bounded by `M_i` and Cauchy-Schwarz `abs_int_cs`/`sum_abs_int_cs`
(`ForcingIBP.lean`), giving `M_i √J_{j+1-i} √J_j`; `A` depends only on `j`. -/
def JTBoundA : Prop :=
  ∀ j : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ (c : ℝ) (V f : Plane → Vec) (G : ℝ) (M : ℕ → ℝ),
    JTHyp c V f G M →
      |jetPair c j f (advB V f)| ≤
        A * ∑ i ∈ Finset.Icc 1 (j + 1),
          M i * Real.sqrt (jetEnergy c (j + 1 - i) f) * Real.sqrt (jetEnergy c j f)

/-- **Leaf (cross term `(f·∇)V`)** (lines 352-358): Leibniz as above; terms `d_S f · d_{∂_m w∖S} V`
with `|S| = s ∈ [0,j]`, `V`-factor bounded by `M_{j+1-s}`, Cauchy-Schwarz gives
`M_i √J_{j+1-i} √J_j` with `i = j+1-s ∈ [1,j+1]`; no cancellation needed. -/
def JTBoundB : Prop :=
  ∀ j : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ (c : ℝ) (V f : Plane → Vec) (G : ℝ) (M : ℕ → ℝ),
    JTHyp c V f G M →
      |jetPair c j f (advB f V)| ≤
        A * ∑ i ∈ Finset.Icc 1 (j + 1),
          M i * Real.sqrt (jetEnergy c (j + 1 - i) f) * Real.sqrt (jetEnergy c j f)

/-- **Leaf (quadratic term)** (lines 352-358): `(f·∇)D^j f` pairs to `0` (`div f = 0`); the
commutator terms `d_{w₁} f · d_{∂_m w₂} f`, `|w₁| = i ≥ 1`, are bounded by Hölder with exponents
`2m/(i-1)`, `2m/(j-i)` (`m = j-1`; `j ≤ 1` direct) and the period-independent `CylGN`
(`cylinder_interpolation_uniform`, `cylJetWord_proof`) applied to the components of `∇f`,
giving `A G ‖D^j f‖²` with `A` independent of `c ≥ 1`. -/
def JTBoundQ : Prop :=
  ∀ j : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ (c : ℝ) (V f : Plane → Vec) (G : ℝ) (M : ℕ → ℝ),
    JTHyp c V f G M → |jetPair c j f (advB f f)| ≤ A * (G * jetEnergy c j f)

theorem jtLin_of (hI : JTAdvInt) (hA : JTBoundA) (hB : JTBoundB) : JTLin := by
  intro j
  obtain ⟨A₁, hA₁, h₁⟩ := hA j
  obtain ⟨A₂, hA₂, h₂⟩ := hB j
  refine ⟨A₁ + A₂, add_nonneg hA₁ hA₂, ?_⟩
  intro c V f G M H
  have H' := H
  obtain ⟨hc, hV, hVp, hVd, hf, hfd, hfb, hG, hM⟩ := H'
  have hfs : ContDiff ℝ ∞ f := hf.1
  have bV : ∀ (w : List Bool) (k : Fin 2), ∃ M' : ℝ, ∀ z : Plane, |wordComp w V k z| ≤ M' :=
    fun w k => ⟨M w.length, hM w k⟩
  have s₁ := contDiff_advB hV hfs
  have s₂ := contDiff_advB hfs hV
  have i₁ := hI j c V f f hV hfs hf (Or.inr hf) bV hfb
  have i₂ := hI j c f V f hfs hV hf (Or.inl hf) hfb bV
  have b₁ := h₁ c V f G M H
  have b₂ := h₂ c V f G M H
  have hsp := jetSplit_proof c j f _ _ s₁ s₂ i₁ i₂
  rw [linTerm_eq hV hfs]
  refine ⟨s₁.add s₂, jetInt_add s₁ s₂ i₁ i₂, ?_⟩
  rw [hsp]
  calc |jetPair c j f (advB V f) + jetPair c j f (advB f V)|
      ≤ |jetPair c j f (advB V f)| + |jetPair c j f (advB f V)| := abs_add_le _ _
    _ ≤ _ := add_le_add b₁ b₂
    _ = _ := by ring

end UnforcedLeray.Short.PartI
