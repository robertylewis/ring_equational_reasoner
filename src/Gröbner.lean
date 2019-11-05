import group_theory.coset ring_theory.ideals data.int.modeq group_theory.quotient_group
       tactic.fin_cases tactic.tidy data.mv_polynomial

open tactic prod native environment interactive lean.parser ideal classical lattice declaration rbtree
local infixl ` ⬝ ` := has_mul.mul
local notation x`²`:99 := x⬝x
local notation ` ` binders ` ↦ ` f:(scoped f, f) := f
local notation `⟮` binders ` ↦ ` f:(scoped f, f) `⟯`:= f

def flip_over_2 {A B C D} (f: A→B→C→D) := z x y ↦ f x y z
infixl ` @₁`:99 := flip
infixl ` @₂`:99 := flip_over_2
infixr ` ∘₂ `:80 := (∘)∘(∘)

instance {X} : monoid (list X) := {
	one := [],
	mul := (++),
	one_mul := by safe,
	mul_one := list.append_nil,
	mul_assoc := list.append_assoc,
}

instance endomonoid {t} : monoid (t → t) := {
	one := id,
	mul := (∘),
	mul_assoc := function.comp.assoc,
	one_mul := function.comp.left_id,
	mul_one := function.comp.right_id,
}

--option.cases_on has typing problems.
def option.maybe {A B} (no: B) (yes: A→B) : option A → B
| none := no
| (some a) := yes a

def ifoldl_help {S T} (f: ℕ→S→T→T) : ℕ → list S → T → T
| i [] r := r
| i (x::s) r := ifoldl_help (i+1) s (f i x r)
def list.ifoldl {S T} (f: ℕ→S→T→T) := ifoldl_help f 0

def list.imap {S T} (f: ℕ→S→T) (s: list S) := (s.ifoldl (list.cons ∘₂ f) []).reverse

universe U
def list.mfilter_map {A B : Type U} {M} [monad M] (f: A → M (option B)) : list A → M (list B)
| [] := pure[]
| (a::s) := do
	fa ← f a,
	s' ← s.mfilter_map,
	pure (fa.maybe s' ⟮b ↦ b::s'⟯)

@[simp] def map₂_default {X Z} (d) (f: X → X → Z) : list X → list X → list Z
| [] [] := []
--| s l := f ((s.nth 0).get_or_else d) ((l.nth 0).get_or_else d) :: map₂_default s.tail l.tail
| [] (y::ys) := f d y :: map₂_default [] ys
| (x::xs) [] := f x d :: map₂_default xs []
| (x::xs) (y::ys) := f x y :: map₂_default xs ys
using_well_founded wf_tacs

def trim_tail {X} [decidable_eq X] (x) (s: list X) := (s.reverse.drop_while (=x)).reverse

--unique_pairs[xⱼ | j] = [(xᵢ,xⱼ) | i<j]
def list.unique_pairs {T} : list T → list (T×T)
| [] := []
| (x::xs) := xs.map⟮y↦ (x,y)⟯ ++ xs.unique_pairs

@[priority 0] instance to_string_of_repr {X} [has_repr X] : has_to_string X := ⟨repr⟩
@[priority 0] meta instance format_of_repr {X} [has_repr X] : has_to_tactic_format X := ⟨has_to_tactic_format.to_tactic_format ∘ repr⟩



-- infixr ` ∷ `:67 := (++)∘repr
-- --set_option pp.all true
-- def replace_1_: list char → string
-- --| ('+'::' '::'-'::s) := "- "++ replace_minus s
-- | [] := ""
-- | (a::s) := match if a≠' ' then none else match s with
-- 	| [] := none
-- 	| (b::s) := if b≠'1' then none else match s with
-- 		| [] := none
-- 		| (c::s) := if c≠' ' then none else
-- 			have hint: s.sizeof < a.val+ (1+s.sizeof), from by {simp[has_lt.lt,nat.lt], rw (_:nat.succ _=0+_), rw (_:1+_=nat.succ _), apply nat.add_le_add_right, tidy, rw nat.add_comm},
-- 			some (' '∷ replace_1_ s)
-- end end with
-- | none := a ∷ replace_1_ s
-- | some s := s


--–Monomials are now represented by lists, which are thought to be zero extended. Trailing zeros are normalized away.
def monomial := list ℕ
namespace monomial

def deg (m: monomial) := list.sum m

def variable_name: ℕ → string
| 0 := "x" | 1 := "y" | 2 := "z"
| n := (char.of_nat (121-n)).to_string

def rise_digit (n: char) := ("⁰¹²³⁴⁵⁶⁷⁸⁹".to_list.nth n.to_string.to_nat).get_or_else '?'
def rise_number (n: string) := (n.to_list.map rise_digit).as_string

instance monomial.has_repr: has_repr monomial := ⟨ m ↦ m.ifoldl⟮j e ↦ ite (e=0) id (++ variable_name j ++ ite (e=1) "" (rise_number (repr e)))⟯ "" ⟩
instance: has_one monomial := ⟨[]⟩
instance: has_mul monomial := ⟨map₂_default 0 (+)⟩ --no need to trim
instance: has_div monomial := ⟨trim_tail 0 ∘₂ map₂_default 0 ⟮x y ↦ x-y⟯⟩

def gcd (n m : monomial) : monomial := trim_tail 0 (list.map₂ min n m) --no need to extend
def lcm (n m : monomial) : monomial := map₂_default 0 max n m --no need to trim

def dvd': monomial → monomial → bool
| [] _ := tt
| (n::ns) m := n ≤ (m.nth 0).get_or_else 0 ∧ dvd' ns m.tail
def dvd := n m ↦ (dvd' n m : Prop)
instance: has_dvd monomial := ⟨dvd⟩
instance: decidable_rel dvd := by unfold dvd; apply_instance


--–Orders should be admissible (unit least and multiplication monotonous).
class order :=
(lt: monomial → monomial → Prop)
(decidable: decidable_rel lt)

def lex: order := {
	lt := list.lex (<),
	decidable := infer_instance,
}
def deg_lex: order := {
	lt := n m ↦ deg n < deg m ∨ (deg n = deg m ∧ list.lex (<) n m),
	decidable := _ _↦ by apply or.decidable,
}
end monomial

@[reducible] private def mo := monomial.order


--–Polynomials (this ended up essentially reimplementing very basics of rbmap equivalently, because I didn't find rbmap early enough)
--Reverse order to have the leading term first.
def poly.less [mo] {K} (x y : K×monomial) := monomial.order.lt y.snd x.snd
def poly[mo] (K)[ring K] := rbtree (K×monomial) poly.less

namespace poly
--K ∈ Type 0 because otherwise combination with tactics gets problematic.
variables {K: Type} [ring K] [decidable_eq K] [o:mo] (P R : poly K)

instance[mo] : has_lt monomial := ⟨monomial.order.lt⟩
instance[mo] : has_le monomial := ⟨ n m ↦ ¬n>m ⟩
instance decidable_lt[mo] : @decidable_rel monomial (<) := monomial.order.decidable
instance decidable_le[mo] : @decidable_rel monomial (≤) := by apply_instance
instance decidable_less: decidable_rel (@less o K) := _ _↦ by unfold less; apply_instance

def coef (m) := ((P.find (0,m)).get_or_else (0,m)).fst
--Value 0 should not be inserted, but rbtree lacks removal rutines. Since full simplification will rebuild a polynomial from scratch, extra zeros should not add up too badly.
def update (m) (f: K→K) : poly K := let k := f (coef P m) in P.insert (k,m)

def monom[mo] (m) : poly K := rbtree_of[m]less
instance[mo] : has_coe monomial (poly K) := ⟨ m↦ monom (1,m) ⟩

--Let f' = (f; 0↦id). Then combine@₂f maps Σ pⱼ⬝mⱼ and Σ rⱼ⬝mⱼ to Σ f' pⱼ rⱼ ⬝ mⱼ (...assuming unsoundly that there's no explicit 0 coefficients...exact behavior depends on what the representation happens to be).
def combine (f: K→K→K) : poly K := P.fold⟮p R' ↦ update R' p.snd (f p.fst)⟯ R
def map_poly (f: K→K) : poly K := combine P P _↦f

instance[mo] : has_zero (poly K) := ⟨rbtree_of[]less⟩
instance[mo] : has_one (poly K) := ⟨monom (1,1)⟩
instance[mo] : has_add (poly K) := ⟨combine @₂ (+)⟩
instance[mo] : has_neg (poly K) := ⟨map_poly @₁ k↦-k⟩
instance[mo] : has_sub (poly K) := ⟨ P R ↦ P + -R ⟩
instance[mo] : has_mul (poly K) := ⟨ P↦ fold⟮m↦ P.fold⟮n↦ (+monom (m⬝n))⟯⟯ @₁0 ⟩
instance[mo] : has_scalar K (poly K) := ⟨ k↦ map_poly @₁ (⬝k) ⟩
instance[mo] : has_pow (poly K) ℕ := ⟨ P n ↦ (list.repeat P n).foldl (⬝)1 ⟩

instance[mo] [has_repr K] : has_repr (poly K) := ⟨ P↦ match P.to_list.filter⟮p:K×_ ↦ p.fst ≠ 0⟯ with
	| [] := "0"
	| (m::ms) := ms.foldl⟮s p ↦ s ++" + "++ repr p.fst ++" "++ repr p.snd⟯ (repr m.fst ++" "++ repr m.snd)
end⟩

def lead_term := (P.fold⟮p:K×_ ↦ option.maybe (if p.fst = 0 then none else some p) some⟯ none).maybe (0,1) id
def lead_coef := P.lead_term.fst
def lead_mono := P.lead_term.snd

def is0 := lead_coef P = 0
instance decidable_is0: decidable P.is0 := by unfold is0; apply_instance

def is_const := lead_mono P = 1
instance decidable_is_const: decidable P.is_const := by unfold is_const; apply_instance

attribute [derive decidable_eq] rbnode

instance[mo] : decidable_eq (poly K) := by apply_instance
instance[mo] : inhabited (poly K) := ⟨0⟩

variable [has_repr K]
def see {X Y} [has_repr X] [has_repr Y] (m:Y) (x:X) := _root_.trace (repr m ++ repr x) x


private def proof[mo] (K)[ring K] := list (poly K)
def poly_mem[mo] (K)[ring K] := poly K × proof K
def polys[mo] (K)[ring K] := list (poly_mem K)

instance hrp[mo] : has_repr (proof K) := by unfold proof; apply_instance--TODO remove after debug

def poly_mem.is0[mo] (P: poly_mem K) := is0 P.fst
instance[mo] (P: poly_mem K) : decidable P.is0 := by unfold poly_mem.is0; apply_instance
instance evvk[mo] : inhabited (poly_mem K) := ⟨ (0,[])⟩

--Construct trivial proof by cloning a proof from non-empty list.
def proof_triv[mo] (B: polys K. assumption) : proof K := B.head.snd.map⟮_↦0⟯
def is_triv[mo] : proof K → bool
| [] := tt
| (p::ps) := is0 p ∧ is_triv ps
def proof_add[mo] (p₁ p₂ : proof K) (f: poly K → poly K) := p₁.map₂ (+) (p₂.map f)

--Compute the S-polynomial of monic polynomials with membership proof.
def monicS[mo] : poly_mem K → poly_mem K → poly_mem K | (P,pP) (R,pR) :=
	let p:= lead_mono P, r:= lead_mono R, m:= p.lcm r, mp:= monom ((1:K), m/p), mr:= monom ((1:K), m/r)
	in (P⬝mp - R⬝mr, proof_add (pP.map (⬝mp)) pR (⬝ (-mr)))


--Accumulates proof to show that if P→R then R - P ∈ ⟨B⟩.
meta def simplify_leading_loop[mo] (B: polys K) : poly_mem K → poly_mem K | (P, proof) :=
	let p := P.lead_mono in match B.filter ((∣p)∘lead_mono∘fst) with
		| [] := (P, proof)
		| (b,prf) ::_ := let c := -monom (lead_coef P, p / lead_mono b) in simplify_leading_loop (P + b⬝c, proof_add proof prf (⬝c))
end
--B must be a non-empty list of monic (and ≠0) polynomials.
meta def simplify_leading[mo] (B: polys K) (P: poly_mem K) : poly_mem K :=
	match B.filter (is_const ∘ fst) with
	| (_,prf) ::_ := (0, proof_add P.snd prf (⬝ (-P.fst)))
	| _ := simplify_leading_loop B P
end

meta def simplify_loop[mo] (B) : poly K → poly_mem K → poly_mem K | R P :=
	if P.is0 then (R, P.snd) else let (P,prf) := simplify_leading B P, p := monom P.lead_term in simplify_loop (R+p) (P-p, prf)
--Return fully simplified R←P and proof that R - P ∈ ⟨B⟩. Input P comes without membership proof, because simplification should be applicable to arbitrary polynomials.
meta def simplify[mo] (B: polys K) (P) := simplify_loop B 0 (P, proof_triv)


variable[field K]
--scale_monic 0 := 0
def scale_monic[mo] : poly_mem K → poly_mem K | (P,prf) := let c := P.lead_coef ⁻¹ in (c•P, prf.map ((•)c))


meta def simplify_basis_loop[mo] (simp: polys K → poly_mem K → poly_mem K) : ℕ → polys K → polys K
| 0 B := B
| l [] := sorry -- l ≤ B.length
| l (P::B) := let
	P' := simp B P,
	B' := ite P'.is0 B (B++[scale_monic P'])
in simplify_basis_loop (if is_triv (P.snd.map₂⟮x y ↦ x-y⟯ P'.snd) then l-1 else B'.length) B'

--For each element of B, if S simplifies the leading term, then simplify additionally with other elements of the basis.
meta def simplify_basis_by[mo] (S: poly_mem K) (B: polys K) := simplify_basis_loop⟮B P ↦ let P' := simplify_leading [S] P in if is_triv P'.snd then P else simplify_leading B P'⟯ B.length B

--Interreduce B.
meta def simplify_basis[mo] (B: polys K) := simplify_basis_loop (simplify_loop @₁0) B.length B


--main loop
private meta def go[mo] : polys K → list (poly_mem K × poly_mem K) → polys K
| G [] := G
| G ( (p₁,p₂) ::ps) := let S := scale_monic (simplify_leading G (monicS p₁ p₂))
	in if S.is0 then go G ps else let G := simplify_basis_by S G in go (S::G) (ps ++ G.map⟮P↦ (P,S)⟯)

meta def «Gröbner basis of»[mo] (B: list (poly K)) := let B := B.filter (not∘is0), B1 := B.imap⟮i b ↦ scale_monic (b, (B.map⟮_↦ (0: poly K)⟯).update_nth i 1)⟯ in simplify_basis (go B1 B1.unique_pairs)
notation `Gröbner_basis_of` := «Gröbner basis of»
--Lean's letter recognition is broken! It is not just an implementation mistake, but it is even specified in an adhoc way – see https://leanprover.github.io/reference/lexical_structure.html#identifiers – which is incompatible with Unicode. Not only a huge number of letters is ignored but also some non-letters included (though correctly called just letterlike) :
def ℡⅋℀ := "Telephone sign ǝʇ “account” are letters only in Lean!"
--Inclusion of non-letters means that Lean can't be said to support a subset of Unicode. FYI: Unicode is about semantics of code points (numbers). UTF-8 is a character encoding (mapping between bytes and numbers) that Lean does use. Observations here hold at the time of writing and hopefully not in the future.


--Tästä voisi johtaa tyyliin ringa-taktiikan. Sievennetään kaikkia ... hmm, miten sievennyskelpoiset lausekkeet määrätään? Kertoimien tulee olla kunnasta, mutta muuttujia saa käsitellä vain rengasoperaatioilla. Teoreettisesti nättiä olisi yleistää hieman ja ratkaista renkaiden ehdolliset sanaongelmat, mutta sehän edellyttäisi paljon lisää koodausta!
--Sitten pitää ratkaista, miten termien triviaali sievennys kuten x+y-x=y hoidetaan. Koska tulos tiedetään aina, voidaan turvallisesti turvautua ring-taktiikkaan.
--Luetaan tavoitetta kunnes vastaan tulee +,⬝,- (tärkeää on, että löydetään maksimaalinen termi sievennettäväksi—tämän pitäisi riittää siihen, koska tietenkään päälioperaatio ei tällöin voi olla jokin sellainen, jota ei osata käsitellä). Huom. - voi esiintyä sekä unaarisena että binäärisenä. Seuraavaksi tarkistetaan, että alitermi on kuntatyyppiä...mutta tämä rajoittaa käytettävyyttä melko merkittävästi. Teoriassa voisi vaatia, että tyyppi on vaihdannainen rengas ja K-moduli jonkin kunnan K suhteen, ja K:lta vaaditaan lisäksi päätettävä yhtyvyys. Jotta tästä teoriasta tulee käytäntöä, lienee vaadittava, että käyttäjä syöttää kunnan (ℚ voi olla oletusarvo).

meta def 𝔼 (pre) := to_expr pre tt ff
--meta def childs (e: expr) := (e.mfoldl⟮c s ↦ [list.cons s c]⟯ []).head
meta def childs: expr → list expr
| (expr.app f p) := [f,p]
| (expr.pi _ _ S T) := [S,T]
| (expr.elet _ t v b) := [t,v,b] --Does this work with infer_type?
| (expr.macro _ cs) := cs
| _ := []

notation `~`x := pure x
notation `ᵘᵖ ` m := monad_lift m


@[reducible] meta def ST := state_t (list expr) tactic
--Run reaction if state is not [].
meta def if_not_found (reaction: ST unit) : ST unit := do s ← state_t.get, when (s=[]) reaction

meta def fbs_loop {T} (t) (test: (expr → ST T) → expr → ST T) (atoms: rb_set expr) : bool → expr → ST unit | layer's_top e :=
when (¬ atoms.contains e) (test⟮x ↦ t<$
	if x≠e then fbs_loop ff x
	else (childs x).mmap' (if_not_found ∘ fbs_loop tt)
⟯ e >> if_not_found (when layer's_top (test⟮e' ↦ when (e≠e') (state_t.put[e]) $>t⟯ e $> ())))
--Finds some minimal subterm accepted by test while treating terms in the set atoms as such. Parameter t is just an inhabitance proof.
meta def find_bottom_simplifiable {T} (t:T) (test) (atoms) : expr → tactic (option expr)
| e := prod.fst <$> (do
	fbs_loop t test atoms tt e,
	g ← state_t.get,
	~ g.nth 0
).run[]


meta def prepare_loop {T} (var: ℕ→T) (test: (expr → ST T) → expr → ST T) : expr → ST T | e :=
test⟮x ↦ if x≠e then prepare_loop x else do
	vs ← state_t.get,
	let i := vs.index_of x,
	when (i = vs.length) (state_t.put (vs++[x])) $> var i
⟯e
--Transform (top layer of) e to its T-representation according to test, with alien subterms replaced by variables generated from var with syntactic equality preserved. Second component of the return value is list of the replaced alien terms.
meta def prepare {T} (var: ℕ→T) (test) (e) := (prepare_loop var test e).run[]
--Like mapping the above, but naming of the alien terms is consistent.
meta def prepares {T} (var: ℕ → T) (test) (es: list expr) := (es.mmap (prepare_loop var test)).run[]


meta def simplify_by_loop {T} (var: ℕ→T) (test: (expr → ST T) → expr → ST T) (simp: expr → T → tactic expr) : rb_set expr → tactic unit | simplified := do
	e ← target,
	x ← find_bottom_simplifiable (var 0) test simplified e,
	x.maybe (~())⟮x ↦ do
		(x',g) ← prepare var test x,
		proof ← simp x x',
		rewrite_target proof,
		`(%%_ = %%s) ← infer_type proof,
		simplify_by_loop (simplified.insert s)⟯

--Warning: in practise this interface turned out to behave ugly! This is a simplifier skeleton whose advantage over simp is that pattern matching and rule selection can be done programmatically. (For example simp could often do nothing with a Gröbner basis represented as simplifying equations, because non-syntactic pattern matching is needed to use them.) This functions like simp only [...]. The actual (single step) simplifier is given as a parameter. Its operation is extended by searching the proof target for simplifiable terms and calling the simplifier for all of these bottom up.
--Parameters
--T: an auxiliarity term representation that the simplifier may choose as it likes.
--var: a stream of distinct variables.
--test recursor ∈ expr → a_monad T : transforms a top operation of an input term into T-representation calling recursor for the childs, or for the whole term if it is alien. See test_poly for an example.
--simp: from original expression E and its T-representation produce a proof that E = simplified E. Failed: Variable var i should be represented by a metavariable whose name ends with mk_numeral i, (or var 0, ..., var n may be represented by quantifying ∀x₀...∀xₙ ???).
meta def simplify_by {T} (var: ℕ→T) (test) (simp) := simplify_by_loop var test simp mk_rb_set
--Notes: Examining term structure and mapping it to T was combined into test. Original term is given to simp, because T-representation may be lossy. However if orig. rep. is needed (Gröbner bases avoid it by using ring), examination of it usually repeats. It even turned out that due to consistent alien term naming the second parameter of simp is practically useless. Currently test can work in ST, though safer would be to require polymorphicity over monad transformer on top of tactic. The tedious part (in addition to the core simplification in T) is producing the proof term in simp. Could this be simplified in a suitable monad?


meta def test_instance (i) := (𝔼 i >>= mk_instance) $> tt <|> ~ff


meta def test_poly[mo] [reflected K] (r: expr → ST (poly K)) (e: expr) : ST (poly K) := match e with
| `(%%x ⬝ %%y) := (⬝) <$> r x <*> r y
| `(%%x + %%y) := (+) <$> r x <*> r y
| `(%%x - %%y) := ⟮x y ↦ x-y⟯ <$> r x <*> r y
| `(- %%x) := ⟮x ↦ -x⟯ <$> r x
| `(%%x ^ %%n) := do
	N ←ᵘᵖ infer_type n,
	if N ≠ `(ℕ) ∨ n.has_var ∨ n.has_local then r e
	else do n ←ᵘᵖ eval_expr ℕ n, (^n) <$> r x
| e := do
	E ←ᵘᵖ infer_type e,
	if E ≠ reflect K ∨ e.has_var ∨ e.has_local then r e
	else do k ←ᵘᵖ eval_expr K e, ~monom (k,[])
end

meta def test_poly_typed[mo] [reflected K] (M: option expr) (r: expr → ST (poly K)) (e) : ST (poly K) := do
	E ←ᵘᵖ infer_type e,
	ok ← match M with some M := ~(E=M : bool)
		| _ :=ᵘᵖ band <$> test_instance``(ring %%E) <*> test_instance``(module %%(reflect K) %%E) end,
	(ite ok test_poly id) r e


--X' i is the iᵗʰ variable "Xᵢ".
def X'[mo] (i:ℕ) : poly K := monom (1, ((list.cons 0)^i) [1])


meta def represent_mono[mo] (r: has_reflect K) (M:expr) (vs: list expr) (m: monomial) : tactic expr :=
	m.ifoldl ⟮x p e ↦ if p=0 then e else do e←e, 𝔼``(%%e ⬝ %%(vs.nth x).iget ^ %%(reflect p))⟯ (𝔼``(1:%%M))

meta def represent_poly[mo] [r: has_reflect K] (M:expr) (vs: list expr) (P: poly K) : tactic expr :=
	P.fold ⟮m e ↦ let c:= m.fst in if c=0 then e else do e←e, mono ← represent_mono r M vs m.snd, 𝔼``(%%e + %%(reflect c)⬝%%mono)⟯ (𝔼``(0:%%M))
--TODO Use module product • to multiply mono by c. Problem is that then ring doesn't work!


meta def local_equations_of_type (M) := do
	ls ← local_context,
	ls.mfilter⟮a ↦ do b ← infer_type a, match b with `(%%x = %%y) := do Y ← infer_type y, ~Y=M | _:=~ff end⟯


--Return a proof of goal found by the given tactic solve.
meta def prove_by (solve: tactic unit) (goal: tactic expr) := do
	n ← get_unused_name,
	goal >>= assert n,
	solve,
	proof ← get_local n,
	--clear proof, --TODO How to clean the local context while keeping proof usable?
	~proof

namespace proof_building_blocks
lemma mul_sub_is_0 {M} [ring M] [module K M] {x y O : M} (c: M) (o0: O=0) (h: x=y) : O - c⬝(x-y) = 0 := by simp[*]

lemma combines {M} [add_comm_group M] [module K M] {P R O : M} (pr: P-R = O) (o0: O = 0) : P = R := by rw (by simp : P = P-R + R);simp[*]

end proof_building_blocks
open proof_building_blocks


--Compute a Gröbner basis from polynomial equations E and return a reducer suitable for simplify_by that uses the computed basis.
meta def verifying_reducer[mo] [reflected K] [r: has_reflect K] (M) (E: list expr) : tactic (expr → poly K → tactic expr) := do
	let test: (expr → ST (poly K)) → _ := test_poly_typed (option.some M),
	be ← E.mmap⟮p ↦ do e ← infer_type p, match e with `(%%x = %%y) := 𝔼``(%%x - %%y) | _:=sorry end⟯,
	((B: list (poly K)), vs) ← prepares X' test be,
	let G := Gröbner_basis_of B,
~ pe _ ↦ do
	--TODO There should be nicer way to keep track of alien subterms. Either variables in polynomials should have arbitrary names (ideal solution) or everything should work inside ST.
	(P, vs) ← (prepare_loop X' test pe).run vs,
	let (R, coef) := simplify G P,
	--R = P + coef•(fⱼ - gⱼ)ⱼ
	--P - R  =ʳⁱⁿᵍ=  -coef•(fⱼ - gⱼ)ⱼ  = “coef•0” = 0  ⟹ P=R
	re ← represent_poly M vs R,
	ce ← coef.mmap(represent_poly M vs),
	K0is0 ← 𝔼``(rfl : (0:%%(reflect K)) = 0),
	step2 ← (ce.zip E).mfoldl ⟮prf cb ↦ 𝔼``(@mul_sub_is_0
		%%(reflect K) infer_instance infer_instance infer_instance infer_instance
		%%M infer_instance infer_instance
		_ _ _ %%cb.fst %%prf %%cb.snd)⟯ K0is0,
	`(%%ce_be = %%_) ← infer_type step2,
	ring_step ← prove_by`[ {ring}] (𝔼``(%%pe - %%re = %%ce_be)),
	𝔼``(@combines
		%%(reflect K) infer_instance infer_instance infer_instance infer_instance
		%%M infer_instance infer_instance
		_ _ _ %%ring_step %%step2)


meta def exactℚ := `[exact ℚ]

meta def ringa (K:Type. exactℚ)[reflected K] [has_reflect K] [field K] [decidable_eq K] [has_repr K/-debug-/] [mo] : tactic unit := do
	t ← target,
	--"find_top_simplifiable" would be more expected behavior...if it existed
	e ← find_bottom_simplifiable (0: poly K) (test_poly_typed none) mk_rb_set t,
	if e=none then fail"nothing to simplify in target" else do
	M ← infer_type e.iget,
	B ← local_equations_of_type M,
	if B=[] then `[ring] else do --Do not fail to preserve composability.
	reducer ← verifying_reducer M B,
	simplify_by (X': ℕ → poly K) (test_poly_typed (some M)) reducer,
	`[try {ring}]


#check Gröbner_basis_of

--Test cases
instance use_this_order := monomial.deg_lex
variables {v x y z : ℚ} {f: ℚ→ℚ}

--These delegate to ring tactic
example: (x+y)⬝(x-y) = x² - y² := by ringa
example: f(2⬝x) = f(x+x) := by ringa
--These don't
example (_:v=z) : (x+y)⬝(x-y) = x² - y² := by ringa
example (_:v=z) : f(2⬝x) = f(x+x) := by ringa

--Core functionality tests
example (_: x+y = z) (_: x² + y² = z²) : x⬝y = 0 := by ringa
example (_: x⬝y² = x+y) (_: x²⬝y = x² + y²) : y^5 = (2⬝x-1)⬝(2⬝y-1)/2 - 1/2 := by ringa
example (_: x⬝y² = x+y) (_: x²⬝y = x+1) : y = x² := by ringa
example (_: z⬝x=y) (_: y=x²) (_: v²=2) : x⬝(2⬝z-x-x) = 0 := by ringa
example (_: x²⬝y = x²) (_: x⬝y² = y²) : (x+y)⬝(x-y) + x² = x^3 := by ringa

.
#exit

--Iteration tests
example (_: x=y) : x⬝f(2⬝x² - y²) - y⬝f(x⬝y) = 0 := by ringa
example (_: x=y) : x⬝f(x-y) - y⬝f(x-x) = 0 := by ringa
example (_: x=y+1) : (x-1)⬝f(2⬝x-1) - y⬝f(x² - y²) = 0 := by ringa
example (_: x²+y² = z²) (_: x^3 + y^3 = z^3) (_: x⬝y = 1) : f(x + y + f(2/3)) = f(f(z²) - 2⬝z) := by ringa

--In algebras over ℚ
open polynomial
example {P: polynomial ℚ} (_: X² - X - 1 = (0: polynomial ℚ)) (_: P = 1-X) : P² = P+1 := by ringa

--Is it worth to handle the situation of inconsistent axioms?
example (_: x²+3⬝x+1 = 0) (_: y²+3⬝y+1 = 0) (_: x^5 + y^5 = 0) : x-y = 1 := by ringa
#check ringa
--∛2̅+̅√̅5̅ + ∛2̅-̅√̅5̅ = 1
--example (_: x²=5) (_: y^3 = 2+x) (_: z^3 = 2-x) : y+z = 1 := by ringa

end poly
open poly

instance {K:Type} [field K] [decidable_eq K] [has_repr K] [mo] : has_repr(poly_mem K) :=
--by unfold poly_mem; apply_instance
⟨ x ↦ repr x.fst ⟩
instance {K:Type} [field K] [decidable_eq K] [has_repr K] [mo] : has_repr(polys K) := by unfold polys; apply_instance

instance use_this := monomial.deg_lex
def lm (m: list ℕ) : poly ℚ := monom (1,m)

def a := lm[2] +3⬝lm[1]+lm[]
def b := lm[0,2] +3⬝lm[0,1]+lm[]
def c := lm[5] + lm[0,5]
#eval simplify(Gröbner_basis_of[a,b]) c
--#eval Gröbner_basis_of[a,b,c] --Time out just because the algorithm is so slow!

def α := lm[0,0,2] + lm[0,2] - lm[2]
def β := lm[0,0,3] + lm[0,3] - lm[3]
def γ := lm[0,1,1] - 1
#eval (Gröbner_basis_of[α,β,γ])
#eval simplify(Gröbner_basis_of[α,β,γ]) (lm[2])

def P := lm[2,1] + ((1:ℚ)/2)•lm[2]
def R := lm[1,2] + lm[0,2]
def S := -lm[2,2] + lm[1,1] + lm[2]
#eval (Gröbner_basis_of[P,R])
#eval simplify (Gröbner_basis_of[P,R]) (S²)

def B := [lm [3] -1, lm[2]+lm[1,1], lm[2]+lm[1,0,1]+lm[0,0,2]]
#eval B
#eval Gröbner_basis_of B
#eval P²⬝R
#eval Gröbner_basis_of$ [lm [3] -1, lm[2]+lm[1,1], lm[2]+lm[1,0,1]+lm[0,0,2], lm [0,3] -1, lm[0,2]+lm[0,1,1]+lm[0,0,2], lm [0,0,3] -1].map(⬝1)
#eval Gröbner_basis_of[lm [3] -1, lm[2]+lm[1,1]+lm[0,2], lm[2]+lm[1,0,1]+lm[0,0,2], lm [0,3] -1, lm[0,2]+lm[0,1,1]+lm[0,0,2], lm [0,0,3] -1]
#eval Gröbner_basis_of(B++[P²⬝R])
--#eval Gröbner_basis_of(P²⬝R::B)

#eval (lm[] + 0).lead_coef
#eval (2⬝lm[4,2] + lm[3,4])².fold((++)∘repr) ""
#eval (2⬝lm[4,2] + lm[3,4])².lead_mono
#eval (P + 3⬝P² + P²)²
