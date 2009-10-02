(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)
Require Export Why.

Require Export Reals.
Require Export Gappa_tactic.

(*Why logic*) Definition lt_real : R -> R -> Prop.
Admitted.

(*Why logic*) Definition le_real : R -> R -> Prop.
Admitted.

(*Why logic*) Definition gt_real : R -> R -> Prop.
Admitted.

(*Why logic*) Definition ge_real : R -> R -> Prop.
Admitted.

(*Why logic*) Definition eq_real : R -> R -> Prop.
Admitted.

(*Why logic*) Definition neq_real : R -> R -> Prop.
Admitted.

(*Why logic*) Definition add_real : R -> R -> R.
Admitted.

(*Why logic*) Definition sub_real : R -> R -> R.
Admitted.

(*Why logic*) Definition mul_real : R -> R -> R.
Admitted.

(*Why logic*) Definition div_real : R -> R -> R.
Admitted.

(*Why logic*) Definition neg_real : R -> R.
Admitted.

(*Why logic*) Definition real_of_int : Z -> R.
Admitted.

(*Why logic*) Definition int_of_real : R -> Z.
Admitted.

(*Why logic*) Definition lt_real_bool : R -> R -> bool.
Admitted.

(*Why logic*) Definition le_real_bool : R -> R -> bool.
Admitted.

(*Why logic*) Definition gt_real_bool : R -> R -> bool.
Admitted.

(*Why logic*) Definition ge_real_bool : R -> R -> bool.
Admitted.

(*Why logic*) Definition eq_real_bool : R -> R -> bool.
Admitted.

(*Why logic*) Definition neq_real_bool : R -> R -> bool.
Admitted.

(*Why axiom*) Lemma lt_real_bool_axiom :
  (forall (x:R), (forall (y:R), ((lt_real_bool x y) = true <-> (Rlt x y)))).
Admitted.

(*Why axiom*) Lemma le_real_bool_axiom :
  (forall (x:R), (forall (y:R), ((le_real_bool x y) = true <-> (Rle x y)))).
Admitted.

(*Why axiom*) Lemma gt_real_bool_axiom :
  (forall (x:R), (forall (y:R), ((gt_real_bool x y) = true <-> (Rgt x y)))).
Admitted.

(*Why axiom*) Lemma ge_real_bool_axiom :
  (forall (x:R), (forall (y:R), ((ge_real_bool x y) = true <-> (Rge x y)))).
Admitted.

(*Why axiom*) Lemma eq_real_bool_axiom :
  (forall (x:R), (forall (y:R), ((eq_real_bool x y) = true <-> (eq x y)))).
Admitted.

(*Why axiom*) Lemma neq_real_bool_axiom :
  (forall (x:R), (forall (y:R), ((neq_real_bool x y) = true <-> ~(eq x y)))).
Admitted.

(*Why logic*) Definition real_max : R -> R -> R.
exact Rmax.
Defined.

(*Why logic*) Definition real_min : R -> R -> R.
Admitted.

(*Why axiom*) Lemma real_max_is_ge :
  (forall (x:R),
   (forall (y:R), (Rge (real_max x y) x) /\ (Rge (real_max x y) y))).
unfold real_max.
intros; split.
apply Rle_ge; apply RmaxLess1.
apply Rle_ge; apply RmaxLess2.
Qed.

(*Why axiom*) Lemma real_max_is_some :
  (forall (x:R),
   (forall (y:R), (eq (real_max x y) x) \/ (eq (real_max x y) y))).
Admitted.

(*Why axiom*) Lemma real_min_is_le :
  (forall (x:R),
   (forall (y:R), (Rle (real_min x y) x) /\ (Rle (real_min x y) y))).
Admitted.

(*Why axiom*) Lemma real_min_is_some :
  (forall (x:R),
   (forall (y:R), (eq (real_min x y) x) \/ (eq (real_min x y) y))).
Admitted.

(*Why logic*) Definition sqrt_real : R -> R.
Admitted.

(*Why logic*) Definition pow_real : R -> R -> R.
Admitted.

(*Why logic*) Definition abs_real : R -> R.
Admitted.

(*Why axiom*) Lemma abs_real_pos :
  (forall (x:R), ((Rge x (0)%R) -> (eq (Rabs x) x))).
Admitted.
Dp_hint abs_real_pos.

(*Why axiom*) Lemma abs_real_neg :
  (forall (x:R), ((Rle x (0)%R) -> (eq (Rabs x) (Ropp x)))).
Admitted.
Dp_hint abs_real_neg.

(*Why logic*) Definition exp : R -> R.
Admitted.

(*Why logic*) Definition log : R -> R.
Admitted.

(*Why logic*) Definition log10 : R -> R.
Admitted.

(*Why axiom*) Lemma log_exp : (forall (x:R), (eq (log (exp x)) x)).
Admitted.
Dp_hint log_exp.

(*Why logic*) Definition cos : R -> R.
Admitted.

(*Why logic*) Definition sin : R -> R.
Admitted.

(*Why logic*) Definition tan : R -> R.
Admitted.

(*Why logic*) Definition cosh : R -> R.
Admitted.

(*Why logic*) Definition sinh : R -> R.
Admitted.

(*Why logic*) Definition tanh : R -> R.
Admitted.

(*Why logic*) Definition acos : R -> R.
Admitted.

(*Why logic*) Definition asin : R -> R.
Admitted.

(*Why logic*) Definition atan : R -> R.
Admitted.

(*Why logic*) Definition atan2 : R -> R -> R.
Admitted.

(*Why logic*) Definition hypot : R -> R -> R.
Admitted.

(*Why axiom*) Lemma prod_pos :
  (forall (x:R),
   (forall (y:R),
    (((Rgt x (0)%R) /\ (Rgt y (0)%R) -> (Rgt (Rmult x y) (0)%R))) /\
    (((Rlt x (0)%R) /\ (Rlt y (0)%R) -> (Rgt (Rmult x y) (0)%R))))).
Admitted.
Dp_hint prod_pos.

(*Why axiom*) Lemma abs_minus :
  (forall (x:R), (eq (Rabs (Ropp x)) (Rabs x))).
Admitted.
Dp_hint abs_minus.

(*Why type*) Definition mode: Set.
Admitted.

(*Why logic*) Definition nearest_even : mode.
Admitted.

(*Why logic*) Definition to_zero : mode.
Admitted.

(*Why logic*) Definition up : mode.
Admitted.

(*Why logic*) Definition down : mode.
Admitted.

(*Why logic*) Definition nearest_away : mode.
Admitted.

(*Why axiom*) Lemma no_other_mode :
  (forall (m:mode), m = nearest_even \/ m = to_zero \/ m = up \/ m = down \/
   m = nearest_away).
Admitted.
Dp_hint no_other_mode.

(*Why axiom*) Lemma mode_distinct :
  ~(nearest_even = to_zero) /\ ~(nearest_even = up) /\
  ~(nearest_even = down) /\ ~(nearest_even = nearest_away) /\
  ~(to_zero = up) /\ ~(to_zero = down) /\ ~(to_zero = nearest_away) /\
  ~(up = down) /\ ~(up = nearest_away) /\ ~(down = nearest_away).
Admitted.
Dp_hint mode_distinct.

(*Why type*) Definition float_format: Set.
Admitted.

(*Why logic*) Definition Single : float_format.
Admitted.

(*Why logic*) Definition Double : float_format.
Admitted.

(*Why logic*) Definition Binary80 : float_format.
Admitted.

(*Why logic*) Definition Quad : float_format.
Admitted.

(*Why type*) Definition gen_float: Set.
Admitted.

(*Why logic*) Definition round_float : float_format -> mode -> R -> R.
Admitted.

(*Why logic*) Definition gen_float_of_real_logic :
  float_format -> mode -> R -> gen_float.
Admitted.

(*Why logic*) Definition float_value : gen_float -> R.
Admitted.

(*Why logic*) Definition exact_value : gen_float -> R.
Admitted.

(*Why logic*) Definition model_value : gen_float -> R.
Admitted.

(*Why logic*) Definition max_gen_float : float_format -> R.
Admitted.

(*Why logic*) Definition min_gen_float : float_format -> R.
Admitted.

(*Why axiom*) Lemma max_single :
  (eq (max_gen_float Single) (33554430 * 10141204801825835211973625643008)%R).
Admitted.
Dp_hint max_single.

(*Why axiom*) Lemma max_double :
  (eq (max_gen_float Double) (9007199254740991 * 19958403095347198116563727130368385660674512604354575415025472424372118918689640657849579654926357010893424468441924952439724379883935936607391717982848314203200056729510856765175377214443629871826533567445439239933308104551208703888888552684480441575071209068757560416423584952303440099278848)%R).
Admitted.
Dp_hint max_double.

(*Why axiom*) Lemma max_binary80 :
  (eq (max_gen_float Binary80) (36893488147419103230 * 32247736798518462797190682400943018516175543670762176328756482144039152568041578530784869838671865972235112113819199496038199562243910663703639216829515817160113666668284961240211417531345524616362428416330602972909073090642506869663645452596715605872599087734040646091573772820166659709055844941963407370586164567373226035331478682139323759030390169756949645512305687629336370321027572205368679114704513230126552642666038554179630426709583211834866442025402779192438955501011599402670474078315979195355085382566505714139685398132788514318516857572135124726246887683817431332595336004485663642818019898976640217306812561246935515065344079842840510097237727080984183495389368072338451606972939196031163096169199428295104133836032565137546925854725960037189363809577708269161078297604210091040361487260740249986383462509936056379514029238590893274747101383360270789838187035523056441182806100163231205084519320466554639512906620717463724499998301458223494983926579429691620482441269711367614363695303004564784940490808737282945526774911719814580226498373894496190363722344710426167299430387657571898023057486643921769603842100563739030336691645389445492926167601553616786810662018623358680430160062641831241724154676346446956483016401282337761290196283249206927902020112758851552032621043952751383985648183664483389113663697474518437837593333184771556767592207983004392544555790253882523577401634907110779490333277898545345116189557099744222039988799226930564811854616377334200980884800664165297389997964692737821895851412532797735108359203559095483310984658106121538922952889055685471125170175723317169593146664295809795623802089889643999415332745683386415868399386033192494319220974648757516356052320358879924313110310884292268260701379338994338108789478905916908161768521947880258489076565694006998844912795108503710046920084170185272761891078021513009632812076867050768977864194042678311369055206891516537021560300798059734220105917788064342240629479094309156746038941015397976356754789446933541512725013448273437547085806482191918607333986763432754828493535124047158138237637409295986872592429450114102485563352324125936266490688770968135131034136174587957527871860195705884826978646394753119840216174117299370924945153580348775272141051491679794666208271496285083069845671716424410676415869955363407007760984457820261218648462922790310801749176357827053037467349708500388630266544397409034371631091896035688733055939026767796894113267574863689692595743405212002418769330858650477320122610373855743251794447804031454470627265691044431863724394790157020749747541055050361466440339407757302440378131261742472589547459292823540674561003306548963849749082270981212995128117275025218442085292281511141515402115396401640539932607790670152400476588736655932035952713596437884630053601152144442487925678513707439322429603512863513937772419859052931939816470086355056926030022478683926998811371487429392139518642533641594848997510779898512138631152276001570189617571577117505003649765241953436949753578990662937482392034476147764320283391607594707828151932952800276998022501766325609849743945881184820529811657759571426179918970334290658333365861701775758750841107251261789710752326125748382152448064208818548133245897789022501048075101440658472328426420634576248281716861120935223755782204696386463154525203556339857062481846160548995002214961818560159651368345845120079053574246560180632466599839315290737648547666905885960618996553045213471557799885589510324494021059895586424571108214444983727593352510360659623694336871156982624856470568852865375380207522670830821369618815960216991366324223164204144978595243245271374275940010359033028897257400300896745451850608529102426268449369972727553520714138832750617641260586748778127838088604132276526159832635929297522815794276302150715627256492836149372994848554854698569272309146920737500425328133816423498307241515119828589935781842076654814684177765311659863765751080177655756714625693102613062094201622809620794125071255386708064848320764949530272433439273743375350030635762736423572793816319775637274418096041530332046157499910206330422447695636005413591515928110703929025624538022689370483285119600899835109936335014160851892197423917205143598214380079070972739838516200090223566115430366326479446523163497707352464003363812601636875414221683002445945525094887495651061394077679898700257734335650549937472988196339378468338812732120356422794395674496874734970810783457481759262704526738373673902304190312120953832926347769566045802798905863532547270355875796602597933585415990415455319622527795552163966597860161185787837154710170391266971001786784354270889004431725527269565131623614750206537270420868165375708343148079210039515648805899537033270890665024179796399141747260973138806486300213292018923538944420046243682707230360249726438817748989930350717709729915628184770113773134324454134693667450204984030027933986759393415283853749497928013737601928987148288)%R).
Admitted.
Dp_hint max_binary80.

(*Why axiom*) Lemma min_single :
  (eq (min_gen_float Single) (1 / 713623846352979940529142984724747568191373312)%R).
Admitted.
Dp_hint min_single.

(*Why axiom*) Lemma min_double :
  (eq (min_gen_float Double) (1 / 202402253307310618352495346718917307049556649764142118356901358027430339567995346891960383701437124495187077864316811911389808737385793476867013399940738509921517424276566361364466907742093216341239767678472745068562007483424692698618103355649159556340810056512358769552333414615230502532186327508646006263307707741093494784)%R).
Admitted.
Dp_hint min_double.

(*Why predicate*) Definition no_overflow  (f:float_format) (m:mode) (x:R)
  := (Rle (Rabs (round_float f m x)) (max_gen_float f)).

(*Why function*) Definition gen_round_error  (x:gen_float)
  := (Rabs (Rminus (float_value x) (exact_value x))).

(*Why function*) Definition gen_relative_error  (x:gen_float)
  := (Rabs (Rdiv (Rminus (float_value x) (exact_value x)) (exact_value x))).

(*Why function*) Definition gen_total_error  (x:gen_float)
  := (Rabs (Rminus (float_value x) (model_value x))).

(*Why axiom*) Lemma bounded_real_no_overflow :
  (forall (f:float_format),
   (forall (m:mode),
    (forall (x:R), ((Rle (Rabs x) (max_gen_float f)) -> (no_overflow f m x))))).
Admitted.
Dp_hint bounded_real_no_overflow.

(*Why axiom*) Lemma bounded_real_overflow_pos :
  (forall (f:float_format),
   (forall (m:mode),
    (forall (x:R),
     ((Rgt x (max_gen_float f)) ->
      ((m = up \/ m = nearest_away -> ~(no_overflow f m x))) /\
      ((m = down \/ m = to_zero -> (eq (round_float f m x) (max_gen_float f)))))))).
Admitted.
Dp_hint bounded_real_overflow_pos.

(*Why axiom*) Lemma bounded_real_overflow_neg :
  (forall (f:float_format),
   (forall (m:mode),
    (forall (x:R),
     ((Rlt x (Ropp (max_gen_float f))) ->
      ((m = down \/ m = nearest_away -> ~(no_overflow f m x))) /\
      ((m = up \/ m = to_zero ->
        (eq (round_float f m x) (Ropp (max_gen_float f))))))))).
Admitted.
Dp_hint bounded_real_overflow_neg.

(*Why axiom*) Lemma bounded_real_overflow_nearest_even :
  (forall (x:R),
   (((Rge (Rabs x) (2 * 340282366920938463463374607431768211456)%R) ->
     ~(no_overflow Single nearest_even x))) /\
   (((Rge (Rabs x)
      (2 * 179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224137216)%R) ->
     ~(no_overflow Double nearest_even x)))).
Admitted.
Dp_hint bounded_real_overflow_nearest_even.

(*Why axiom*) Lemma round_greater_max :
  (forall (f:float_format),
   (forall (m:mode),
    (forall (x:R), (~(no_overflow f m x) -> (Rgt (Rabs x) (max_gen_float f)))))).
Admitted.
Dp_hint round_greater_max.

(*Why axiom*) Lemma positive_constant :
  (forall (f:float_format),
   (forall (m:mode),
    (forall (x:R),
     ((Rle (min_gen_float f) x) /\ (Rle x (max_gen_float f)) ->
      (no_overflow f m x) /\ (Rgt (round_float f m x) (0)%R))))).
Admitted.
Dp_hint positive_constant.

(*Why axiom*) Lemma negative_constant :
  (forall (f:float_format),
   (forall (m:mode),
    (forall (x:R),
     ((Rle (Ropp (max_gen_float f)) x) /\ (Rle x (Ropp (min_gen_float f))) ->
      (no_overflow f m x) /\ (Rlt (round_float f m x) (0)%R))))).
Admitted.
Dp_hint negative_constant.

(*Why axiom*) Lemma round_increasing :
  (forall (f:float_format),
   (forall (m:mode),
    (forall (x:R),
     (forall (y:R),
      ((Rle x y) -> (Rle (round_float f m x) (round_float f m y))))))).
Admitted.
Dp_hint round_increasing.

(*Why axiom*) Lemma round_greater_min :
  (forall (f:float_format),
   (forall (m:mode),
    (forall (x:R),
     ((Rge (Rabs x) (min_gen_float f)) ->
      (Rge (Rabs (round_float f m x)) (min_gen_float f)))))).
Admitted.
Dp_hint round_greater_min.

(*Why axiom*) Lemma round_less_min_pos :
  (forall (f:float_format),
   (forall (m:mode),
    (forall (x:R),
     ((Rlt (0)%R x) /\ (Rlt x (min_gen_float f)) ->
      ((m = up \/ m = nearest_away ->
        (eq (round_float f m x) (min_gen_float f)))) /\
      ((m = down \/ m = to_zero -> (eq (round_float f m x) (0)%R))))))).
Admitted.
Dp_hint round_less_min_pos.

(*Why axiom*) Lemma round_less_min_neg :
  (forall (f:float_format),
   (forall (m:mode),
    (forall (x:R),
     ((Rlt (Ropp (min_gen_float f)) x) /\ (Rlt x (0)%R) ->
      ((m = down \/ m = nearest_away ->
        (eq (round_float f m x) (Ropp (min_gen_float f))))) /\
      ((m = up \/ m = to_zero -> (eq (round_float f m x) (0)%R))))))).
Admitted.
Dp_hint round_less_min_neg.

(*Why axiom*) Lemma round_less_min_nearest_even :
  (forall (x:R),
   (((Rle (Rabs x) (2 / 1427247692705959881058285969449495136382746624)%R) ->
     (eq (round_float Single nearest_even x) (0)%R))) /\
   (((Rle (Rabs x)
      (2 / 404804506614621236704990693437834614099113299528284236713802716054860679135990693783920767402874248990374155728633623822779617474771586953734026799881477019843034848553132722728933815484186432682479535356945490137124014966849385397236206711298319112681620113024717539104666829230461005064372655017292012526615415482186989568)%R) ->
     (eq (round_float Double nearest_even x) (0)%R)))).
Admitted.
Dp_hint round_less_min_nearest_even.

(*Why axiom*) Lemma round_of_zero :
  (forall (f:float_format),
   (forall (m:mode), (eq (round_float f m (0)%R) (0)%R))).
Admitted.
Dp_hint round_of_zero.

(*Why axiom*) Lemma round_down_le :
  (forall (f:float_format), (forall (x:R), (Rle (round_float f down x) x))).
Admitted.
Dp_hint round_down_le.

(*Why axiom*) Lemma round_up_ge :
  (forall (f:float_format), (forall (x:R), (Rge (round_float f up x) x))).
Admitted.
Dp_hint round_up_ge.

(*Why axiom*) Lemma round_down_neg :
  (forall (f:float_format),
   (forall (x:R),
    (eq (round_float f down (Ropp x)) (Ropp (round_float f up x))))).
Admitted.
Dp_hint round_down_neg.

(*Why axiom*) Lemma round_up_neg :
  (forall (f:float_format),
   (forall (x:R),
    (eq (round_float f up (Ropp x)) (Ropp (round_float f down x))))).
Admitted.
Dp_hint round_up_neg.

(*Why axiom*) Lemma round_idempotent :
  (forall (f:float_format),
   (forall (m1:mode),
    (forall (m2:mode),
     (forall (x:R),
      (eq (round_float f m1 (round_float f m2 x)) (round_float f m2 x)))))).
Admitted.
Dp_hint round_idempotent.

Admitted.
Dp_hint prod_pos.

Admitted.
Dp_hint abs_minus.

Admitted.
Dp_hint help.

(*Why axiom*) Lemma help1 :
  (forall (x:R),
   (forall (y:R),
    (forall (z:R),
     (forall (t:R),
      (((Rle (0)%R x) /\ (Rle x y)) /\ (Rle (0)%R z) /\ (Rle z t) ->
       (Rle (Rmult x z) (Rmult y t))))))).
Admitted.
Dp_hint help1.

Admitted.
Dp_hint help2.

Admitted.
Dp_hint help2_.

Admitted.
Dp_hint help2__.

(*Why axiom*) Lemma help3 :
  (forall (x:R),
   (forall (y:R),
    (forall (a:R),
     (forall (b:R),
      (((Rle (0)%R a) /\ (Rle a x)) /\ (Rle y b) /\ (Rlt y (0)%R) ->
       (Rle (Rmult x y) (Rmult a b))))))).
Admitted.
Dp_hint help3.

Admitted.
Dp_hint help4.

Admitted.
Dp_hint help4_.

Admitted.
Dp_hint help4__.

(*Why axiom*) Lemma help5 :
  (forall (x:R),
   (forall (y:R),
    (forall (a:R),
     (forall (b:R),
      ((Rle a x) /\ (Rgt x (0)%R) /\ (Rle y b) /\ (Rle b (0)%R) ->
       (Rle (Rmult x y) (Rmult a b))))))).
Admitted.
Dp_hint help5.

(*Why axiom*) Lemma help6 :
  (forall (x:R),
   (forall (y:R),
    (forall (a:R),
     (forall (b:R),
      ((Rle b y) /\ (Rgt y (0)%R) /\ (Rle x a) /\ (Rle a (0)%R) ->
       (Rle (Rmult x y) (Rmult a b))))))).
Admitted.
Dp_hint help6.

(*Why axiom*) Lemma help7 :
  (forall (x:R),
   (forall (y:R),
    (forall (a:R),
     (forall (b:R),
      (((Rle x a) /\ (Rle a (0)%R)) /\ (Rle y b) /\ (Rlt y (0)%R) ->
       (Rle (Rmult a b) (Rmult x y))))))).
Admitted.
Dp_hint help7.

(*Why axiom*) Lemma help8 :
  (forall (x:R),
   (forall (y:R),
    (forall (a:R),
     (forall (b:R),
      ((Rle x a) /\ (Rlt x (0)%R) /\ (Rle y b) /\ (Rle b (0)%R) ->
       (Rle (Rmult a b) (Rmult x y))))))).
Admitted.
Dp_hint help8.

(*Why axiom*) Lemma help9 :
  (forall (x:R),
   (forall (y:R),
    (forall (a:R),
     (forall (b:R),
      ((Rle a x) /\ (Rgt x (0)%R) /\ (Rle (0)%R b) /\ (Rle b y) ->
       (Rle (Rmult a b) (Rmult x y))))))).
Admitted.
Dp_hint help9.

(*Why axiom*) Lemma help10 :
  (forall (x:R),
   (forall (y:R),
    (forall (z:R),
     ((Rle (0)%R x) /\ (Rle y z) -> (Rle (Rmult x y) (Rmult x z)))))).
Admitted.
Dp_hint help10.

(*Why axiom*) Lemma help11 :
  (forall (x:R),
   (forall (y:R),
    (forall (z:R),
     ((Rlt (0)%R x) /\ (Rle y z) -> (Rle (Rmult x y) (Rmult x z)))))).
Admitted.
Dp_hint help11.

(*Why axiom*) Lemma help12 :
  (forall (x:R),
   (forall (y:R),
    (forall (z:R),
     ((Rlt (0)%R x) /\ (Rlt y z) -> (Rlt (Rmult x y) (Rmult x z)))))).
Admitted.
Dp_hint help12.

(*Why axiom*) Lemma help13 :
  (forall (x:R),
   (forall (y:R),
    (forall (z:R),
     ((Rle (0)%R x) /\ (Rlt y z) -> (Rle (Rmult x y) (Rmult x z)))))).
Admitted.
Dp_hint help13.

(*Why axiom*) Lemma help14 :
  (forall (x:R),
   (forall (y:R),
    (forall (z:R),
     ((Rle x (0)%R) /\ (Rle y z) -> (Rge (Rmult x y) (Rmult x z)))))).
Admitted.
Dp_hint help14.

(*Why axiom*) Lemma help15 :
  (forall (x:R),
   (forall (y:R),
    (forall (z:R),
     ((Rlt x (0)%R) /\ (Rle y z) -> (Rge (Rmult x y) (Rmult x z)))))).
Admitted.
Dp_hint help15.

(*Why axiom*) Lemma help16 :
  (forall (x:R),
   (forall (y:R),
    (forall (z:R),
     ((Rlt x (0)%R) /\ (Rlt y z) -> (Rgt (Rmult x y) (Rmult x z)))))).
Admitted.
Dp_hint help16.

(*Why axiom*) Lemma help17 :
  (forall (x:R),
   (forall (y:R),
    (forall (z:R),
     ((Rle x (0)%R) /\ (Rlt y z) -> (Rge (Rmult x y) (Rmult x z)))))).
Admitted.
Dp_hint help17.

(*Why axiom*) Lemma ttt :
  (forall (x:gen_float),
   ((Rgt (float_value x) (0)%R) -> ~(eq (float_value x) (0)%R))).
Admitted.
Dp_hint ttt.

