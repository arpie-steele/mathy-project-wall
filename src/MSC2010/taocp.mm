$[ set.mm $]

$(
                             ~~ PUBLIC DOMAIN ~~
  This work is waived of all rights, including copyright, according to the CC0
  Public Domain Dedication.  http://creativecommons.org/publicdomain/zero/1.0/
$)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                Mathbox for Richard Penner
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Propositions from _The Art of Computer Programming_ Volume 1
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

$)

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     _The Art of Computer Programming_ Notes on the Exercises
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Mappings:
  <HTML>
  <dl compact>
    <dt>floor(rating/5) :</dt>
        <dd>2 -> (0, 60], 4 -> [900, 1200], 6 -> [7200, Inf)</dd>
    <dt>rating mod 5 :</dt>
        <dd>0 -> < 20% work details, 4 -> > 80% work is details</dd>
    <dt>rating <= 45 :</dt>
        <dd>known solution</dd>
    <dt>M :</dt>
        <dd>exercise involves mathematical concepts</dd>
    <dt>HM :</dt>
        <dd>exercise involves mathematical concepts from calculus
            or similar</dd>
    <dt>&#9654; :</dt>
        <dd>Recommended</dd>
  </dl>
  </HTML>

 Exercises :

 1. &#91;00] What does the rating "M20" mean?

The exercise is mathematically oriented and should take 15 minutes
to complete.

 2. &#91;10] Of what value can the exercises in a textbook be to the reader?

Exercises test knowledge transfer, ability to work with knowledge
transferred and introduce new topics where the knowledge is
discoverable, but not necessarily spelled out.

$)

  ${
    $d k ph $.  $d k A $.  $d k B $.  $d k C $.  $d k N $.
    rp-ex3gen.a $e |- ( ph -> A e. CC ) $.
    rp-ex3gen.b $e |- ( ph -> B e. CC ) $.
    rp-ex3gen.c $e |- ( ph -> C e. CC ) $.
    rp-ex3gen.d $e |- ( ph -> D = ( ( B x. A ) + C ) ) $.
    rp-ex3gen.n $e |- ( ph -> N e. NN0 ) $.
    $( Prove that 13^3 = 2197.  Generalize your answer.

       Exercise 3 of [KnuthTAOCP1] p.  XX

       (Contributed by Richard Penner, 5-Nov-2019.) $)
    rp-ex3gen $p |- ( ph -> ( D ^ N )
                            = sum_ k e. ( 0 ... N )
                                   ( ( N _C k )
                                     x. ( ( ( B ^ ( N - k ) )
                                            x. ( A ^ ( N - k ) ) )
                                          x. ( C ^ k ) ) ) ) $=
  ( cexp co cmul cc0 csu cc wcel cn0 caddc cfz cv cmin oveq1d wceq mulcld binom
  cbc syl3anc wa adantr cle wbr elfznn0 adantl simpl elfzle2 3jca sylan nn0sub2
  w3a syl mulexpd oveq2d sumeq2dv 3eqtrd ) AEGMNCBONZDUANZGMNZPGUBNZGFUCZUINZVH
  GVLUDNZMNZDVLMNZONZONZFQZVKVMCVNMNBVNMNONZVPONZONZFQAEVIGMKUEAVHRSDRSGTSZVJVS
  UFACBIHUGJLVHDFGUHUJAVKVRWBFAVLVKSZUKZVQWAVMOWEVOVTVPOWECBVNACRSWDIULABRSWDHU
  LWEVLTSZWCVLGUMUNZVBZVNTSAWCWDWHLWCWDUKWFWCWGWDWFWCVLGUOUPWCWDUQWDWGWCVLPGURU
  PUSUTVLGVAVCVDUEVEVFVG $.

  $}

  ${
    rp-decadd0i.a $e |- A e. CC $.
    rp-decadd0i.b $e |- B e. CC $.
    rp-decadd0i.c $e |- C e. CC $.
    rp-decadd0i.d $e |- ( A + B ) = D $.
    $( Simplify certain decimal sums.
       (Contributed by Richard Penner, 6-Nov-2019.) $)
    rp-decadd0i $p |- ( ; A 0 + ; B C ) = ; D C $=
      ( cc0 cdc caddc co c10 cmul df-dec 10re recni mulcli eqtri eqcomi addid1i
      oveq12i oveq2i adddii oveq1i addassi ) AIJZBCJZKLMANLZMBNLZCKLZKLZDCJZUGU
      IUHUKKUGUIIKLUIAIOUIMAMPQZERZUASBCOUBUMULUMMDNLZCKLZULDCOUQUIUJKLZCKLULUP
      URCKUPMABKLZNLURDUSMNUSDHTUCMABUNEFUDSUEUIUJCUOMBUNFRGUFSSTS $.
  $}

  $(
    This statement isn't used enough to shorten total proofs.
  ${
    rp-ex3lem1.a $e |- A e. CC $.
    rp-ex3lem1.b $e |- B e. CC $.
    rp-ex3lem1 $p |-  ( k e. ( 0 ... N )
                        -> ( ( N _C k )
                             x. ( ( ( 10 ^ ( N - k ) ) x. ( A ^ ( N - k ) ) )
                                  x. ( B ^ k ) ) ) e. CC ) $=
      ( cv cc0 cfz co wcel cbc c10 cmin cexp cmul cc a1i expcld mulcld fznn0sub
      bccl2 nncnd 10nn nncni elfznn0 ) CGZHDIJKZDUGLJZMDUGNJZOJZAUJOJZPJZBUGOJZ
      PJUHUIUGDUBUCUHUMUNUHUKULUHMUJMQKUHMUDUERUGHDUAZSUHAUJAQKUHERUOSTUHBUGBQK
      UHFRUGDUFSTT $.
  $}
  $)

  $( Prove that 13^3 = 2197.
     (Contributed by Richard Penner, 6-Nov-2019.) $)
  rp-ex3 $p |- ( ; 1 3 ^ 3 ) = ; ; ; 2 1 9 7 $=
    ( vk c1 c3 cdc cexp co cc0 c10 cmul caddc c2 c9 c7 wceq wtru wcel 3cn eqtri
    oveq2i oveq12i cfz cv cbc cmin csu 1cnd 10nn nncni a1i df-dec cn0 rp-ex3gen
    cc 3nn0 trud cuz cfv cz cle wbr 0z 0re 3re 3pos ltleii eluz2 mpbir3an bccl2
    nncnd fznn0sub expcld mulcld elfznn0 adantl oveq2 oveq2d oveq12d bcn0 ax-mp
    3z subid1i df-3 2cn ax-1cn addcomi 1nn0 2nn0 expadd mp3an exp1 sqvali dec10
    3eqtri decnncl2 nnnn0i dec0u 1exp mulid1i exp0 mulid2i syl6eq fsum1p oveq1i
    1nn 0p1e1 sumeq1i 1z 1le3 wa wss 1eluzge0 fzss1 sseli syl bcn1 3m1e2 mulcli
    sq1 mulcomi 3t3e9 mulassi 9cn mulcomli 9nn0 0nn0 deccl 3eqtr3i 1p1e2 2z 2re
    2lt3 2eluzge0 bccmpl mp2an 2p1e3 nn0cni expcl numexp0 7cn rp-decadd0i leidi
    subaddrii 9t3e27 eqtr3i 7nn0 cn nn0fz0 mpbi nn0sub2 fsum1 bcnn subidi 10nn0
    sq3 1t1e1 3exp3 addassi 7p2e9 3eqtr4i 9p2e11 ) BCDZCEFZGCUAFZCAUBZUCFZHCUVD
    UDFZEFZBUVFEFZIFZCUVDEFZIFZIFZAUEZBGDZGDZGDZGBJFZCUAFZUVLAUEZJFZKBDZLDZMDZU
    VBUVMNOBHCUVAACOUFHUMPZOHUGUHZUICUMPZOQUIUVAHBIFZCJFNOBCUJUICUKPZOUNUIULUOU
    VMUVTNOUVLUVPAGCCGUPUQZPZOUWJGURPCURPZGCUSUTVAVTGCVBVCVDVEGCVFVGUIUVDUVCPZU
    VLUMPZOUWLUVEUVKUWLUVEUVDCVHVIUWLUVIUVJUWLUVGUVHUWLHUVFUWDUWLUWEUIUVDGCVJZV
    KUWLBUVFUWLUFUWNVKVLUWLCUVDUWFUWLQUIUVDCVMVKVLVLZVNUVDGNZUVLCGUCFZHCGUDFZEF
    ZBUWREFZIFZCGEFZIFZIFZUVPUWPUVEUWQUVKUXCIUVDGCUCVOUWPUVIUXAUVJUXBIUWPUVGUWS
    UVHUWTIUWPUVFUWRHEUVDGCUDVOZVPUWPUVFUWRBEUXEVPVQUVDGCEVOVQVQUXDBUVPIFUVPUWQ
    BUXCUVPIUWHUWQBNUNCVRVSUXCUVPBIFZUVPUXAUVPUXBBIUXAUXFUVPUWSUVPUWTBIUWSHCEFZ
    UVPUWRCHECQWAZSUXGHHUVNIFZIFZHUVOIFUVPUXGHBKJFZEFZHBEFZHKEFZIFZUXJCUXKHECKB
    JFZUXKWBKBWCWDWERSUWDBUKPKUKPUXLUXONUWEWFWGHBKWHWIUXMHUXNUXIIUWDUXMHNUWEHWJ
    VSZUXNHHIFZUXIHUWEWKZHUVNHIWLSRTWMUXIUVOHIUVNUVNBXDWNZWOWPSUVOUVOUVNUXTWNZW
    OWPWMRUWTBCEFZBUWRCBEUXHSUWKUYBBNVTCWQVSRTUVPUVPUVOUYAWNUHZWRZRUWFUXBBNQCWS
    VSTUYDRTUVPUYCWTRXAXBUOUVTUVPBBDZLDZMDZJFUWCUVSUYGUVPJUVSBCUAFZUVLAUEZLGDZG
    DZBBJFZCUAFZUVLAUEZJFZUYGUVRUYHUVLAUVQBCUAXEXCXFUYIUYONOUVLUYKABCCBUPUQPZOU
    YPBURPUWKBCUSUTXGVTXHBCVFVGUIOUVDUYHPZXIUWLUWMUYQUWLOUYHUVCUVDBUWIPUYHUVCXJ
    XKBGCXLVSXMVNUWOXNUVDBNZUVLCBUCFZHCBUDFZEFZBUYTEFZIFZCBEFZIFZIFZUYKUYRUVEUY
    SUVKVUEIUVDBCUCVOUYRUVIVUCUVJVUDIUYRUVGVUAUVHVUBIUYRUVFUYTHEUVDBCUDVOZVPUYR
    UVFUYTBEVUGVPVQUVDBCEVOVQVQVUFCCUXRIFZIFZUYKUYSCVUEVUHIUWHUYSCNUNCXOVSZVUEU
    XRCIFVUHVUCUXRVUDCIVUCUXRBIFUXRVUAUXRVUBBIVUAUXNUXRUYTKHEXPSUXSRVUBBKEFBUYT
    KBEXPSXRRTUXRHHUWEUWEXQZWRRUWFVUDCNQCWJVSTUXRCVUKQXSRTCCIFZUXRIFLUXRIFZVUIU
    YKVULLUXRIXTXCCCUXRQQVUKYAVUMHHLIFZIFZHUYJIFUYKUXRLVUOVUKYBHHLUWEUWEYBYAYCV
    UNUYJHILYDWPSUYJLGYDYEYFZWPWMYGRXAXBUOUYOUYKKLDZMDZJFUYGUYNVURUYKJUYNKCUAFZ
    UVLAUEZKMDZGDZUXPCUAFZUVLAUEZJFZVURUYMVUSUVLAUYLKCUAYHXCXFVUTVVENOUVLVVBAKC
    CKUPUQPZOVVFKURPZUWKKCUSUTYIVTKCYJVCYKVEKCVFVGUIOUVDVUSPZXIUWLUWMVVHUWLOVUS
    UVCUVDKUWIPVUSUVCXJYLKGCXLVSXMVNUWOXNUVDKNZUVLCKUCFZHCKUDFZEFZBVVKEFZIFZCKE
    FZIFZIFZVVBVVIUVEVVJUVKVVPIUVDKCUCVOVVIUVIVVNUVJVVOIVVIUVGVVLUVHVVMIVVIUVFV
    VKHEUVDKCUDVOZVPVVIUVFVVKBEVVRVPVQUVDKCEVOVQVQVVQCLHIFZIFZVVBVVJCVVPVVSIVVJ
    CVVKUCFZUYSCUWHVVGVVJVWANUNYIKCYMYNVVKBCUCCKBQWCWDYOUUBZSVUJWMVVPVUNVVSVVNH
    VVOLIVVNUWGHVVLHVVMBIVVLUXMHVVKBHEVWBSUXQRVVMBBEFZBVVKBBEVWBSBUMPZVWCBNWDBW
    JVSRTHUWEWRRUUNTHLUWEYBXSRTVVTVVAHIFZHVVAIFVVBCLIFZHIFVVTVWECLHQYBUWEYAVWFV
    VAHILCVVAYBQUUCYCXCUUDVVAHVVAKMWGUUEYFZYPZUWEXSVVAVWGWPWMRXAXBUOVVEVVBVVAJF
    VURVVDVVAVVBJVVDCCUAFZUVLAUEZCCUCFZHCCUDFZEFZBVWLEFZIFZCCEFZIFZIFZVVAVVCVWI
    UVLAUXPCCUAYOXCXFUWKVWRUMPVWJVWRNVTVWKVWQVWKCUVCPZVWKUUFPUWHVWSUNCUUGUUHCCV
    HVSUHVWOVWPVWMVWNUWDVWLUKPZVWMUMPUWEUWHUWHCCUSUTVWTUNUNCVCUUACCUUIWIZHVWLYQ
    YNVWDVWTVWNUMPWDVXABVWLYQYNXQUWFUWHVWPUMPQUNCCYQYNXQXQUVLVWRACUVDCNZUVEVWKU
    VKVWQIUVDCCUCVOVXBUVIVWOUVJVWPIVXBUVGVWMUVHVWNIVXBUVFVWLHEUVDCCUDVOZVPVXBUV
    FVWLBEVXCVPVQUVDCCEVOVQVQUUJYNVWRBVVAIFZVVAVWKBVWQVVAIUWHVWKBNUNCUUKVSVWQVX
    DVVAVWOBVWPVVAIVWOBBIFBVWMBVWNBIVWMHGEFBVWLGHECQUULZSHUUMYRRVWNBGEFBVWLGBEV
    XESBWFYRRTUUORUUPTVVAVWHWTZRTVXFRWMSVVAKMVUQVWHWCYSHKIFZMJFZKJFZVXGLJFZVVAK
    JFVUQVXIVXGMKJFZJFVXJVXGMKHKUWEWCXQYSWCUUQVXKLVXGJUURSRVVAVXHKJKMUJXCKLUJUU
    SYTRWMSUYJVUQMUYFUYJVUPYPVUQKLWGYDYFYPYSLKLUYEYBWCYBUUTYTYTRWMSUVOUYFMUWBUV
    OUVNGBGWFYEYFZYEYFYPUYFUYELBBWFWFYFZYDYFYPYSUVNUYELUWAUVNVXLYPUYEVXMYPYBBBB
    KWDWDWDYHYTYTYTRWM $.

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     _The Art of Computer Programming_ Section 1.1 Algorithms
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     _The Art of Computer Programming_ Section 1.2 Mathematical Preliminaries
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     _The Art of Computer Programming_ Section 1.2.1 Mathematical Induction
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
_The Art of Computer Programming_ Section 1.2.2 Numbers, Powers, and Logarithms
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     _The Art of Computer Programming_ Section 1.2.3 Sums and Products
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     _The Art of Computer Programming_ Section 1.2.4 Integer Functions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     _The Art of Computer Programming_ Section 1.2.4 Elementary Number Theory
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
    _The Art of Computer Programming_ Section 1.2.5 Permutations and Factorials
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     _The Art of Computer Programming_ Section 1.2.6 Binomial Coefficients
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     _The Art of Computer Programming_ Section 1.2.7 Harmonic Numbers
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     _The Art of Computer Programming_ Section 1.2.8 Fibonacci Numbers
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     _The Art of Computer Programming_ Section 1.2.9 Generating Functions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     _The Art of Computer Programming_ Section 1.2.10 Analysis of an Algorithm
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
    _The Art of Computer Programming_ Section 1.2.11 Asymptotic Representations
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     _The Art of Computer Programming_ Section 1.2.11.1 The O-notation
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     Section 1.2.11.2. Euler's summation formula
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
   Section 1.2.11.3. Some asymptotic calculations
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     _The Art of Computer Programming_ Section 1.3 MIX
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     _The Art of Computer Programming_ Section 1.3.1 Description of MIX
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     _The Art of Computer Programming_ Section 1.3.2. The MIX Assembly Language
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  _The Art of Computer Programming_ Section 1.3.3. Applications to Permutations
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     Section 1.4. Some Fundamental Programming Techniques
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     _The Art of Computer Programming_ Section 1.4.1. Subroutines
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

