$[ set.mm $]

$(
  Add to #bib section of mmset.raw.html :

  <LI><A NAME="Bruck1971"></A> [Bruck1971] Richard Hubert Bruck, <I>A Survey
  of Binary Systems</I>, 3rd Edition, Springer-Verlag Berlin Heidelberg
  (1971);</LI>

  Add to Typsetting definitions :

  htmldef "PBO" as " PartialBinOp ";
    althtmldef "PBO" as " PartialBinOp ";
    latexdef "PBO" as " {\rm PartialBinOp} ";
  htmldef "PMgm" as " PartialMagma ";
    althtmldef "PMgm" as " PartialMagma ";
    latexdef "PMgm" as " {\rm PartialMagma} ";
  htmldef "C_PM" as " <IMG SRC='subseteq.gif' WIDTH=12 HEIGHT=19 ALT=' C_' TITLE='C_'><sub>PM</sub> ";
    althtmldef "C_PM" as "  &#8838;<sub>PM</sub> ";
    latexdef "C_PM" as " \subseteq_{\rm PM} ";
  htmldef "MgmNEW" as " MagmaNEW ";
    althtmldef "MgmNEW" as " MagmaNEW ";
    latexdef "MgmNEW" as " {\rm MagmaNEW} ";
  htmldef "MgmRP" as " MagmaRP ";
    althtmldef "MgmRP" as " MagmaRP ";
    latexdef "MgmRP" as " {\rm MagmaRP} ";
  htmldef "C_Mgm" as " <IMG SRC='subseteq.gif' WIDTH=12 HEIGHT=19 ALT=' C_' TITLE='C_'><sub>Mgm</sub> ";
    althtmldef "C_Mgm" as "  &#8838;<sub>Mgm</sub> ";
    latexdef "C_Mgm" as " \subseteq_{\rm Mgm} ";

$)

$(
###############################################################################
                ZF (ZERMELO-FRAENKEL) SET THEORY
###############################################################################
$)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
             ZF Set Theory - add the Axiom of Power Sets
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                                 Functions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
                   Single-Valued Mappings and Partial Binary Operations
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  A "single-valued mapping" is a function from its domain into a
  class. Here we simply use the definition ~ df-f and restrict
  domain or range to sets if required.

  A "partial binary operation" on a set, ` G ` is a single-valued
  mapping from a subset of the Cartesian product ` ( G X. G ) `
  into ` G ` .

$)

  $c PBO $.
  $( Partial binary operation. $)
  cpbo $a class PBO $.

  ${
    $d g h x A $.  $d g h x G $.  $d g h x H $.

    $( A single-valued mapping ` A ` of a set ` G ` into a set ` H ` is a
       correspondence which assigns to each ` g ` in ` G ` a unique element
       ` ( A `` g ) ` in ` H ` .

       Definition of [Bruck1971] p. 1 (Contributed by Richard Penner,
       28-Sep-2019.) $)
    fveu2 $p |- ( A : G --> H -> A. g e. G E! h e. H ( A ` g ) = h ) $=
      cG cH cA wf vg cv cA cfv vh cv wceq vh cH wreu vg cG cG cH cA wf cA cG
      wfn cA crn cH wss wa vg cv cG wcel vg cv cA cfv vh cv wceq vh cH wreu wi
      cG cH cA df-f cA cG wfn cA crn cH wss vg cv cG wcel vg cv cA cfv vh cv
      wceq vh cH wreu cA cG wfn cA crn cH wss vg cv cG wcel w3a vh cv cH wcel
      vg cv cA cfv vh cv wceq wa vh weu vg cv cA cfv vh cv wceq vh cH wreu cA
      cG wfn cA crn cH wss vg cv cG wcel w3a vh cv cH wcel vg cv cA cfv vh cv
      wceq wa vh vx weq wb vh wal vx wex vh cv cH wcel vg cv cA cfv vh cv wceq
      wa vh weu cA cG wfn cA crn cH wss vg cv cG wcel w3a vh cv cH wcel vg cv
      cA cfv vh cv wceq wa vh vx weq wb vh wal vx vg cv cA cfv vx cv wceq cA cG
      wfn cA crn cH wss vg cv cG wcel w3a vh cv cH wcel vg cv cA cfv vh cv wceq
      wa vh vx weq wb vh wal wi vx vx cv vg cv cA cfv wceq vg cv cA cfv vx cv
      wceq vx vx vg cv cA cfv vg cv cA fvex isseti vx cv vg cv cA cfv wceq vg
      cv cA cfv vx cv wceq vx cv vg cv cA cfv eqcom biimpi eximii vg cv cA cfv
      vx cv wceq cA cG wfn cA crn cH wss vg cv cG wcel w3a vh cv cH wcel vg cv
      cA cfv vh cv wceq wa vh vx weq wb vh vg cv cA cfv vx cv wceq cA cG wfn cA
      crn cH wss vg cv cG wcel w3a vh cv cH wcel vg cv cA cfv vh cv wceq wa vh
      vx weq vg cv cA cfv vx cv wceq cA cG wfn cA crn cH wss vg cv cG wcel w3a
      vh cv cH wcel vg cv cA cfv vh cv wceq wa vh vx weq vg cv cA cfv vx cv
      wceq vh cv cH wcel vg cv cA cfv vh cv wceq wa vh vx weq cA cG wfn cA crn
      cH wss vg cv cG wcel w3a vg cv cA cfv vx cv wceq vg cv cA cfv vh cv wceq
      vh vx weq vh cv cH wcel vg cv cA cfv vh cv wceq vg cv cA cfv vx cv wceq
      vh vx weq vg cv cA cfv vh cv vx cv eqtr2 ancoms adantrl 3adant2 3exp vg
      cv cA cfv vx cv wceq cA cG wfn cA crn cH wss vg cv cG wcel w3a vh vx weq
      vh cv cH wcel vg cv cA cfv vh cv wceq wa vg cv cA cfv vx cv wceq cA cG
      wfn cA crn cH wss vg cv cG wcel w3a vh vx weq w3a vh cv cH wcel vg cv cA
      cfv vh cv wceq vg cv cA cfv vx cv wceq cA cG wfn cA crn cH wss vg cv cG
      wcel w3a vh vx weq vh cv cH wcel cA cG wfn cA crn cH wss vg cv cG wcel
      w3a vg cv cA cfv vx cv wceq vh vx weq vh cv cH wcel wi cA cG wfn cA crn
      cH wss vg cv cG wcel vg cv cA cfv vx cv wceq vh vx weq vh cv cH wcel wi
      wi cA cG wfn vg cv cG wcel cA crn cH wss vg cv cA cfv vx cv wceq vh vx
      weq vh cv cH wcel wi wi cA cG wfn vg cv cG wcel cA crn cH wss vg cv cA
      cfv vx cv wceq vh vx weq vh cv cH wcel wi wi wi cA cG wfn vg cv cG wcel
      wa vg cv cA cfv cA crn wcel cA crn cH wss vg cv cA cfv vx cv wceq vh vx
      weq vh cv cH wcel wi wi wi cG vg cv cA fnfvelrn cA crn cH wss vg cv cA
      cfv cA crn wcel vg cv cA cfv vx cv wceq vh vx weq vh cv cH wcel wi wi cA
      crn cH wss vg cv cA cfv cA crn wcel wa vg cv cA cfv cH wcel vg cv cA cfv
      vx cv wceq vh vx weq vh cv cH wcel wi wi cA crn cH vg cv cA cfv ssel2 vh
      vx weq vg cv cA cfv vx cv wceq vg cv cA cfv cH wcel vh cv cH wcel vh vx
      weq vg cv cA cfv vx cv wceq vg cv cA cfv cH wcel vh cv cH wcel wi vh vx
      weq vg cv cA cfv vx cv wceq wa vh cv vg cv cA cfv wceq vg cv cA cfv cH
      wcel vh cv cH wcel wi vh cv vg cv cA cfv vx cv eqtr3 vg cv cA cfv cH wcel
      vh cv cH wcel wi vg cv cA cfv vh cv vg cv cA cfv vh cv wceq vg cv cA cfv
      cH wcel vh cv cH wcel vg cv cA cfv vh cv cH eleq1 biimpd eqcoms syl ex
      com13 syl expcom syl ex com23 3imp com12 3imp vg cv cA cfv vx cv wceq vh
      vx weq vg cv cA cfv vh cv wceq cA cG wfn cA crn cH wss vg cv cG wcel w3a
      vg cv cA cfv vh cv vx cv eqtr3 3adant2 jca 3exp impbidd alrimdv eximii
      19.37aiv vh cv cH wcel vg cv cA cfv vh cv wceq wa vh vx df-eu sylibr vg
      cv cA cfv vh cv wceq vh cH df-reu sylibr 3expia sylbi ralrimiv $.

  $}

  ${
    $d g A $.  $d g B $.  $d g G $.  $d g H $.

    $( If ` A , B ` are single-valued mappings of ` G ` into ` H ` then
       ` A = B ` if and only if ` ( A `` g ) = ( B `` g ) ` for every ` g ` in
       ` G ` .  See ~ eqfnfv .

       Remark of [Bruck1971] p. 1 (Contributed by Richard Penner,
       26-Sep-2019.) $)
    eqffv $p |- ( ( A : G --> H /\ B : G --> H ) -> ( A = B <->
              A. g e. G ( A ` g ) = ( B ` g ) ) ) $=
      cG cH cA wf cA cG wfn cB cG wfn cA cB wceq vg cv cA cfv vg cv cB cfv wceq
      vg cG wral wb cG cH cB wf cG cH cA ffn cG cH cB ffn vg cG cA cB eqfnfv
      syl2an $.
  $}

  ${
    $( We allow the possibility that ` G ` may be the empty set.

       Remark of [Bruck1971] p. 1

       (Contributed by Richard Penner, 26-Sep-2019.) $)
    0fex $p |- ( ( A : G --> H /\ G = (/) ) -> A e. _V ) $=
    cG c0 wceq cG cH cA wf cG cvv wcel cA cvv wcel c0 cvv wcel cG c0 wceq cG
    cvv wcel wi 0ex c0 cvv cG eleq1a ax-mp cG cH cvv cA fex sylan2 $.
  $}

  ${
  $( If ` G , H ` are non-empty sets, the logical product
     ` G X. H ` is the set of all ordered pairs ` <. a , b >. ` ,
     ` a ` in ` G ` , ` b ` in ` H ` , where
     ` <. a , b >. = <. c , d >. ` if and only if ` a = c ` , ` b = d ` .
     See ~ df-xp and ~ opthg .

     Remark of [Bruck1971] p. 1
  $)
  $}

  ${
    $d x y u v $.
    $( By a (single-valued) _partial binary operation_ ` A ` on the (non-empty)
       set ` G ` we mean a single-valued mapping ` A ` from some subset
       ` dom A ` of ` G X. G ` into ` G ` .  Here ` dom A ` is the is the
       _domain_ of ` A ` ;

       (_Note_:  Bruck uses _range_ for what Metamath calls ` dom ` .  See
       ~ df-dm .)

       Definition binary operation in [Bruck1971] p. 1 $)
    df-pbo $a |- PBO = { <. x , y >. | ( y =/= (/) /\ x C_ ( ( y X. y ) X. y ) /\ A. u E* v u x v ) } $.
  $}

  ${
    $d x y u v $.
    $( Partial Binary Operation is a relation.  (Contributed by Richard Penner,
       28-Sep-2019.) $)
    relpbo $p |- Rel PBO $=
      vy cv c0 wne vx cv vy cv vy cv cxp vy cv cxp wss vu cv vv cv vx cv wbr vv
      wmo vu wal w3a vx vy cpbo vx vy vv vu df-pbo relopabi $.
  $}

  ${
    $( If classes are related by Partial Binary Operation, both classes are
       sets.  (Contributed by Richard Penner, 28-Sep-2019.) $)
    pbocv $p |- ( A PBO B -> ( A e. _V /\ B e. _V ) ) $=
      cpbo wrel cA cB cpbo wbr cA cvv wcel cB cvv wcel wa relpbo cA cB cpbo
      brrelex12 mpan $.
  $}

  ${
    $d u v x y A $.  $d x y B $.
    $( Partial Binary Operation relation.  (Contributed by Richard Penner,
       28-Sep-2019.) $)
    brpbo $p |- ( A PBO B <-> ( ( A e. _V /\ B e. _V ) /\ ( B =/= (/) /\ A C_ ( ( B X. B ) X. B ) /\ A. u E* v u A v ) ) ) $=
      cA cB cpbo wbr cA cvv wcel cB cvv wcel wa cA cvv wcel cB cvv wcel wa cB
      c0 wne cA cB cB cxp cB cxp wss vu cv vv cv cA wbr vv wmo vu wal w3a wa cA
      cB pbocv cA cvv wcel cB cvv wcel wa cB c0 wne cA cB cB cxp cB cxp wss vu
      cv vv cv cA wbr vv wmo vu wal w3a simpl vy cv c0 wne vx cv vy cv vy cv
      cxp vy cv cxp wss vu cv vv cv vx cv wbr vv wmo vu wal w3a cA cvv wcel vy
      cv c0 wne cA vy cv vy cv cxp vy cv cxp wss vu cv vv cv cA wbr vv wmo vu
      wal w3a wa cA cvv wcel cB cvv wcel wa cB c0 wne cA cB cB cxp cB cxp wss
      vu cv vv cv cA wbr vv wmo vu wal w3a wa vx vy cA cB cvv cvv cpbo vx cv cA
      wceq vy cv c0 wne vx cv vy cv vy cv cxp vy cv cxp wss vu cv vv cv vx cv
      wbr vv wmo vu wal w3a cA cvv wcel vy cv c0 wne cA vy cv vy cv cxp vy cv
      cxp wss vu cv vv cv cA wbr vv wmo vu wal w3a wa vx cv cA wceq vy cv c0
      wne vx cv vy cv vy cv cxp vy cv cxp wss vu cv vv cv vx cv wbr vv wmo vu
      wal w3a vy cv c0 wne cA vy cv vy cv cxp vy cv cxp wss vu cv vv cv cA wbr
      vv wmo vu wal w3a cA cvv wcel vx cv cA wceq vy cv c0 wne vy cv c0 wne vx
      cv vy cv vy cv cxp vy cv cxp wss cA vy cv vy cv cxp vy cv cxp wss vu cv
      vv cv vx cv wbr vv wmo vu wal vu cv vv cv cA wbr vv wmo vu wal vx cv cA
      wceq vy cv c0 wne idd vx cv cA wceq vx cv vy cv vy cv cxp vy cv cxp wss
      cA vy cv vy cv cxp vy cv cxp wss vx cv cA vy cv vy cv cxp vy cv cxp sseq1
      biimpd vx cv cA wceq vu cv vv cv vx cv wbr vv wmo vu wal vu cv vv cv cA
      wbr vv wmo vu wal vx cv cA wceq vu cv vv cv vx cv wbr vv wmo vu cv vv cv
      cA wbr vv wmo vu vx cv cA wceq vu cv vv cv vx cv wbr vu cv vv cv cA wbr
      vv vu cv vv cv vx cv cA breq mobidv albidv biimpd 3anim123d vx cA
      eqvisset jctild vx cv cA wceq vy cv c0 wne cA vy cv vy cv cxp vy cv cxp
      wss vu cv vv cv cA wbr vv wmo vu wal w3a vy cv c0 wne vx cv vy cv vy cv
      cxp vy cv cxp wss vu cv vv cv vx cv wbr vv wmo vu wal w3a cA cvv wcel vy
      cv c0 wne cA vy cv vy cv cxp vy cv cxp wss vu cv vv cv cA wbr vv wmo vu
      wal w3a vy cv c0 wne vx cv vy cv vy cv cxp vy cv cxp wss vu cv vv cv vx
      cv wbr vv wmo vu wal w3a wi cA vx cv cA vx cv wceq vy cv c0 wne vy cv c0
      wne cA vy cv vy cv cxp vy cv cxp wss vx cv vy cv vy cv cxp vy cv cxp wss
      vu cv vv cv cA wbr vv wmo vu wal vu cv vv cv vx cv wbr vv wmo vu wal cA
      vx cv wceq vy cv c0 wne idd cA vx cv wceq cA vy cv vy cv cxp vy cv cxp
      wss vx cv vy cv vy cv cxp vy cv cxp wss cA vx cv vy cv vy cv cxp vy cv
      cxp sseq1 biimpd cA vx cv wceq vu cv vv cv cA wbr vv wmo vu wal vu cv vv
      cv vx cv wbr vv wmo vu wal cA vx cv wceq vu cv vv cv cA wbr vv wmo vu cv
      vv cv vx cv wbr vv wmo vu cA vx cv wceq vu cv vv cv cA wbr vu cv vv cv vx
      cv wbr vv vu cv vv cv cA vx cv breq mobidv albidv biimpd 3anim123d eqcoms
      adantld impbid vy cv cB wceq cA cvv wcel vy cv c0 wne cA vy cv vy cv cxp
      vy cv cxp wss vu cv vv cv cA wbr vv wmo vu wal w3a wa cA cvv wcel cB cvv
      wcel wa cB c0 wne cA cB cB cxp cB cxp wss vu cv vv cv cA wbr vv wmo vu
      wal w3a wa vy cv cB wceq cA cvv wcel cA cvv wcel cB cvv wcel wa vy cv c0
      wne cA vy cv vy cv cxp vy cv cxp wss vu cv vv cv cA wbr vv wmo vu wal w3a
      cB c0 wne cA cB cB cxp cB cxp wss vu cv vv cv cA wbr vv wmo vu wal w3a vy
      cv cB wceq cB cvv wcel cA cvv wcel cA cvv wcel cB cvv wcel wa wi vy cB
      eqvisset cB cvv wcel cA cvv wcel pm3.21 syl vy cv cB wceq vy cv c0 wne cB
      c0 wne cA vy cv vy cv cxp vy cv cxp wss cA cB cB cxp cB cxp wss vu cv vv
      cv cA wbr vv wmo vu wal vu cv vv cv cA wbr vv wmo vu wal vy cv cB wceq vy
      cv c0 wne cB c0 wne vy cv cB c0 neeq1 biimpd vy cv cB wceq cA vy cv vy cv
      cxp vy cv cxp wss cA cB cB cxp cB cxp wss vy cv cB wceq vy cv vy cv cxp
      vy cv cxp cB cB cxp cB cxp cA vy cv cB wceq vy cv vy cv cxp cB cB cxp vy
      cv cB vy cv cB wceq vy cv cB vy cv cB vy cv cB wceq id vy cv cB wceq id
      xpeq12d vy cv cB wceq id xpeq12d sseq2d biimpd vy cv cB wceq vu cv vv cv
      cA wbr vv wmo vu wal idd 3anim123d anim12d cA cvv wcel cB cvv wcel wa cB
      c0 wne cA cB cB cxp cB cxp wss vu cv vv cv cA wbr vv wmo vu wal w3a wa cA
      cvv wcel vy cv c0 wne cA vy cv vy cv cxp vy cv cxp wss vu cv vv cv cA wbr
      vv wmo vu wal w3a wa wi cB vy cv cB vy cv wceq cA cvv wcel cB cvv wcel wa
      cA cvv wcel cB c0 wne cA cB cB cxp cB cxp wss vu cv vv cv cA wbr vv wmo
      vu wal w3a vy cv c0 wne cA vy cv vy cv cxp vy cv cxp wss vu cv vv cv cA
      wbr vv wmo vu wal w3a cA cvv wcel cB cvv wcel wa cA cvv wcel wi cB vy cv
      wceq cA cvv wcel cB cvv wcel simpl a1i cB vy cv wceq cB c0 wne vy cv c0
      wne cA cB cB cxp cB cxp wss cA vy cv vy cv cxp vy cv cxp wss vu cv vv cv
      cA wbr vv wmo vu wal vu cv vv cv cA wbr vv wmo vu wal cB vy cv wceq cB c0
      wne vy cv c0 wne cB vy cv c0 neeq1 biimpd cB vy cv wceq cA cB cB cxp cB
      cxp wss cA vy cv vy cv cxp vy cv cxp wss cB vy cv wceq cB cB cxp cB cxp
      vy cv vy cv cxp vy cv cxp cA cB vy cv wceq cB cB cxp vy cv vy cv cxp cB
      vy cv cB vy cv wceq cB vy cv cB vy cv cB vy cv wceq id cB vy cv wceq id
      xpeq12d cB vy cv wceq id xpeq12d sseq2d biimpd cB vy cv wceq vu cv vv cv
      cA wbr vv wmo vu wal idd 3anim123d anim12d eqcoms impbid vx vy vv vu
      df-pbo brabg pm5.21nii $.
  $}

  ${
    $d A u v $.
    $( Partial Binary Operation relation.  (Contributed by Richard Penner,
       28-Sep-2019.) $)
    brpbo2 $p |- ( A PBO B <-> ( ( A e. _V /\ B e. _V ) /\ ( B =/= (/) /\ A C_ ( ( B X. B ) X. B ) /\ Fun A ) ) ) $=
      cA cB cpbo wbr cA cvv wcel cB cvv wcel wa cB c0 wne cA cB cB cxp cB cxp
      wss vu cv vv cv cA wbr vv wmo vu wal w3a wa cA cvv wcel cB cvv wcel wa cB
      c0 wne cA cB cB cxp cB cxp wss cA wfun w3a wa vv vu cA cB brpbo cB c0 wne
      cA cB cB cxp cB cxp wss vu cv vv cv cA wbr vv wmo vu wal w3a cB c0 wne cA
      cB cB cxp cB cxp wss cA wfun w3a cA cvv wcel cB cvv wcel wa cB c0 wne cA
      cB cB cxp cB cxp wss vu cv vv cv cA wbr vv wmo vu wal w3a cB c0 wne cA cB
      cB cxp cB cxp wss cA wfun w3a cB c0 wne cA cB cB cxp cB cxp wss vu cv vv
      cv cA wbr vv wmo vu wal w3a cB c0 wne cA cB cB cxp cB cxp wss cA wfun cB
      c0 wne cA cB cB cxp cB cxp wss vu cv vv cv cA wbr vv wmo vu wal simp1 cB
      c0 wne cA cB cB cxp cB cxp wss vu cv vv cv cA wbr vv wmo vu wal simp2 cA
      cB cB cxp cB cxp wss vu cv vv cv cA wbr vv wmo vu wal cA wfun cB c0 wne
      cA cB cB cxp cB cxp wss vu cv vv cv cA wbr vv wmo vu wal wa cA wrel vu cv
      vv cv cA wbr vv wmo vu wal wa cA wfun cA cB cB cxp cB cxp wss cA wrel vu
      cv vv cv cA wbr vv wmo vu wal cA cB cB cxp cB cxp wss cA cvv cvv cxp wss
      cA wrel cA cB cB cxp cB cxp wss cB cB cxp cB cxp cvv cvv cxp wss cA cvv
      cvv cxp wss cB cB cxp cB xpss cA cB cB cxp cB cxp cvv cvv cxp sstr2 mpi
      cA df-rel sylibr anim1i vu vv cA dffun6 sylibr 3adant1 3jca cA wfun vu cv
      vv cv cA wbr vv wmo vu wal cB c0 wne cA cB cB cxp cB cxp wss cA wfun cA
      wrel vu cv vv cv cA wbr vv wmo vu wal vu vv cA dffun6 simprbi 3anim3i
      impbii anbi2i bitri $.
  $}

  ${
    $d d A $.  $d d B $.
    $( Partial Binary Operation relation.  (Contributed by Richard Penner,
       29-Sep-2019.) $)
    brpbo3 $p |- ( A PBO B <-> ( ( A e. _V /\ B e. _V ) /\ B =/= (/) /\ E. d ( d C_ ( B X. B ) /\ A : d --> B ) ) ) $=
      cA cB cpbo wbr cA cvv wcel cB cvv wcel wa cB c0 wne cA cB cB cxp cB cxp
      wss cA wfun w3a wa cA cvv wcel cB cvv wcel wa cB c0 wne vd cv cB cB cxp
      wss vd cv cB cA wf wa vd wex w3a cA cB brpbo2 cA cvv wcel cB cvv wcel wa
      cB c0 wne cA cB cB cxp cB cxp wss cA wfun w3a wa cA cvv wcel cB cvv wcel
      wa cB c0 wne vd cv cB cB cxp wss vd cv cB cA wf wa vd wex w3a cA cvv wcel
      cB cvv wcel wa cB c0 wne cA cB cB cxp cB cxp wss cA wfun w3a cA cvv wcel
      cB cvv wcel wa cB c0 wne vd cv cB cB cxp wss vd cv cB cA wf wa vd wex w3a
      cA cvv wcel cB cvv wcel wa cB c0 wne cA cB cB cxp cB cxp wss cA wfun w3a
      cA cvv wcel cB cvv wcel wa cB c0 wne vd cv cB cB cxp wss vd cv cB cA wf
      wa vd wex cA cvv wcel cB cvv wcel wa cB c0 wne cA cB cB cxp cB cxp wss cA
      wfun w3a ax-1 cB c0 wne cA cB cB cxp cB cxp wss cA wfun w3a cB c0 wne wi
      cA cvv wcel cB cvv wcel wa cB c0 wne cA cB cB cxp cB cxp wss cA wfun
      simp1 a1i cB c0 wne cA cB cB cxp cB cxp wss cA wfun w3a cA wfun cA cdm cB
      cB cxp wss cA crn cB wss w3a cA cvv wcel cB cvv wcel wa vd cv cB cB cxp
      wss vd cv cB cA wf wa vd wex cA cB cB cxp cB cxp wss cA wfun cA wfun cA
      cdm cB cB cxp wss cA crn cB wss w3a cB c0 wne cA cB cB cxp cB cxp wss cA
      wfun wa cA wfun cA cdm cB cB cxp wss cA crn cB wss cA cB cB cxp cB cxp
      wss cA wfun simpr cA cB cB cxp cB cxp wss cA cdm cB cB cxp wss cA wfun cA
      cB cB cxp cB cxp wss cA cdm cB cB cxp cB cxp cdm cB cB cxp cA cB cB cxp
      cB cxp dmss cB cB cxp cB dmxpss syl6ss adantr cA cB cB cxp cB cxp wss cA
      crn cB wss cA wfun cA cB cB cxp cB cxp wss cA crn cB cB cxp cB cxp crn cB
      cA cB cB cxp cB cxp rnss cB cB cxp cB rnxpss syl6ss adantr 3jca 3adant1
      cA cvv wcel cB cvv wcel wa vd cv cB cB cxp wss vd cv cB cA wf wa cA wfun
      cA cdm cB cB cxp wss cA crn cB wss w3a vd cA cdm cvv cA cvv wcel cA cdm
      cvv wcel cB cvv wcel cA cvv dmexg adantr vd cv cA cdm wceq cA wfun cA cdm
      cB cB cxp wss cA crn cB wss w3a vd cv cB cB cxp wss vd cv cB cA wf wa wi
      cA cvv wcel cB cvv wcel wa vd cv cA cdm wceq cA wfun cA cdm cB cB cxp wss
      cA crn cB wss w3a vd cv cB cB cxp wss vd cv cB cA wf cA wfun cA cdm cB cB
      cxp wss cA crn cB wss w3a vd cv cB cB cxp wss vd cv cA cdm wceq cA cdm cB
      cB cxp wss cA wfun cA cdm cB cB cxp wss cA crn cB wss simp2 vd cv cA cdm
      cB cB cxp sseq1 syl5ibr cA wfun cA cdm cB cB cxp wss cA crn cB wss w3a vd
      cv cA cdm wceq vd cv cB cA wf cA wfun cA cdm cB cB cxp wss cA crn cB wss
      vd cv cA cdm wceq vd cv cB cA wf wi cA wfun cA crn cB wss vd cv cA cdm
      wceq vd cv cB cA wf wi wi cA cdm cB cB cxp wss cA wfun cA crn cB wss vd
      cv cA cdm wceq vd cv cB cA wf cA wfun cA crn cB wss vd cv cA cdm wceq w3a
      cA vd cv wfn cA crn cB wss vd cv cB cA wf cA wfun cA crn cB wss vd cv cA
      cdm wceq w3a cA wfun cA cdm vd cv wceq cA vd cv wfn cA wfun cA crn cB wss
      vd cv cA cdm wceq simp1 cA wfun cA crn cB wss vd cv cA cdm wceq w3a vd cv
      cA cdm cA wfun cA crn cB wss vd cv cA cdm wceq simp3 eqcomd cA vd cv
      df-fn sylanbrc cA wfun cA crn cB wss vd cv cA cdm wceq simp2 vd cv cB cA
      df-f sylanbrc 3exp a1d 3imp com12 jcad adantl spcimedv syl5 3jcad imp cA
      cvv wcel cB cvv wcel wa cB c0 wne vd cv cB cB cxp wss vd cv cB cA wf wa
      vd wex w3a cA cvv wcel cB cvv wcel wa cB c0 wne cA cB cB cxp cB cxp wss
      cA wfun w3a cA cvv wcel cB cvv wcel wa cB c0 wne vd cv cB cB cxp wss vd
      cv cB cA wf wa vd wex simp1 cA cvv wcel cB cvv wcel wa cB c0 wne vd cv cB
      cB cxp wss vd cv cB cA wf wa vd wex w3a cB c0 wne cA cB cB cxp cB cxp wss
      cA wfun wa cB c0 wne cA cB cB cxp cB cxp wss cA wfun w3a cA cvv wcel cB
      cvv wcel wa cB c0 wne vd cv cB cB cxp wss vd cv cB cA wf wa vd wex simp2
      vd cv cB cB cxp wss vd cv cB cA wf wa vd wex cA cvv wcel cB cvv wcel wa
      cA cB cB cxp cB cxp wss cA wfun wa cB c0 wne vd cv cB cB cxp wss vd cv cB
      cA wf wa cA cB cB cxp cB cxp wss cA wfun wa vd vd cv cB cB cxp wss vd cv
      cB cA wf wa cA cB cB cxp cB cxp wss cA wfun vd cv cB cA wf vd cv cB cB
      cxp wss cA vd cv cB cxp cB cB cxp cB cxp vd cv cB cA fssxp vd cv cB cB
      cxp cB xpss1 sylan9ssr vd cv cB cA wf cA wfun vd cv cB cB cxp wss vd cv
      cB cA ffun adantl jca exlimiv 3ad2ant3 cB c0 wne cA cB cB cxp cB cxp wss
      cA wfun 3anass sylanbrc jca impbii bitri $.
  $}

  ${
    $d b A $.  $d b x y $.  $d u v x y $.
    $( we allow the possibility that ` dom A ` may be empty.

       Remark of [Bruck1971] p. 1 (Contributed by Richard Penner,
       28-Sep-2019.) $)
    pbodm0 $p |- ( A = (/) -> A. b ( b =/= (/) -> ( A PBO b /\ dom A = (/) ) ) ) $=
      cA c0 wceq vb cv c0 wne cA vb cv cpbo wbr cA cdm c0 wceq wa wi vb cA c0
      wceq vb cv c0 wne cA vb cv cpbo wbr cA cdm c0 wceq cA c0 wceq vb cv c0
      wne cA vb cv cop cpbo wcel cA vb cv cpbo wbr cA c0 wceq cA vb cv cop c0
      vb cv cop wceq vb cv c0 wne cA vb cv cop cpbo wcel wi cA c0 vb cv opeq1
      vb cv c0 wne cA vb cv cop cpbo wcel cA vb cv cop c0 vb cv cop wceq c0 vb
      cv cop cpbo wcel vb cv c0 wne c0 vb cv cop vy cv c0 wne vx cv vy cv vy cv
      cxp vy cv cxp wss vu cv vv cv vx cv wbr vv wmo vu wal w3a vx vy copab
      cpbo vb cv c0 wne vy cv c0 wne vx cv vy cv vy cv cxp vy cv cxp wss vu cv
      vv cv vx cv wbr vv wmo vu wal w3a vy vb cv wsbc vx c0 wsbc c0 vb cv cop
      vy cv c0 wne vx cv vy cv vy cv cxp vy cv cxp wss vu cv vv cv vx cv wbr vv
      wmo vu wal w3a vx vy copab wcel vb cv c0 wne vb cv c0 wne c0 vb cv vb cv
      cxp vb cv cxp wss vu cv vv cv c0 wbr vv wmo vu wal vy cv c0 wne vx cv vy
      cv vy cv cxp vy cv cxp wss vu cv vv cv vx cv wbr vv wmo vu wal w3a vy vb
      cv wsbc vx c0 wsbc vb cv c0 wne id c0 vb cv vb cv cxp vb cv cxp wss vb cv
      c0 wne vb cv vb cv cxp vb cv cxp 0ss a1i vu cv vv cv c0 wbr vv wmo vu wal
      vb cv c0 wne vu cv vv cv c0 wbr vv wmo vu vu cv vv cv c0 wbr vv wmo vu cv
      vv cv c0 wbr vv wex vu cv vv cv c0 wbr vv weu wi vu cv vv cv c0 wbr vv
      wex vu cv vv cv c0 wbr vv weu vu cv vv cv c0 wbr vv vu cv vv cv br0 nex
      pm2.21i vu cv vv cv c0 wbr vv df-mo mpbir ax-gen a1i vy cv c0 wne vx cv
      vy cv vy cv cxp vy cv cxp wss vu cv vv cv vx cv wbr vv wmo vu wal w3a vb
      cv c0 wne c0 vb cv vb cv cxp vb cv cxp wss vu cv vv cv c0 wbr vv wmo vu
      wal w3a vx vy c0 vb cv 0ex vb vex vx cv c0 wceq vy vb weq wa vy cv c0 wne
      vb cv c0 wne vx cv vy cv vy cv cxp vy cv cxp wss c0 vb cv vb cv cxp vb cv
      cxp wss vu cv vv cv vx cv wbr vv wmo vu wal vu cv vv cv c0 wbr vv wmo vu
      wal vy vb weq vy cv c0 wne vb cv c0 wne wb vx cv c0 wceq vy cv vb cv c0
      neeq1 adantl vx cv c0 wceq vx cv vy cv vy cv cxp vy cv cxp wss c0 vb cv
      vb cv cxp vb cv cxp wss wb vy vb weq vx cv c0 wceq vx cv vy cv vy cv cxp
      vy cv cxp wss c0 vb cv vb cv cxp vb cv cxp wss vx cv c0 wceq vx cv vy cv
      vy cv cxp vy cv cxp wss c0 vy cv vy cv cxp vy cv cxp wss vy cv vy cv cxp
      vy cv cxp 0ss vx cv c0 vy cv vy cv cxp vy cv cxp sseq1 mpbiri c0 vb cv vb
      cv cxp vb cv cxp wss vx cv c0 wceq vb cv vb cv cxp vb cv cxp 0ss a1i 2thd
      adantr vx cv c0 wceq vu cv vv cv vx cv wbr vv wmo vu wal vu cv vv cv c0
      wbr vv wmo vu wal wb vy vb weq vx cv c0 wceq vu cv vv cv vx cv wbr vv wmo
      vu cv vv cv c0 wbr vv wmo vu vx cv c0 wceq vu cv vv cv vx cv wbr vu cv vv
      cv c0 wbr vv vu cv vv cv vx cv c0 breq mobidv albidv adantr 3anbi123d
      sbc2ie syl3anbrc vy cv c0 wne vx cv vy cv vy cv cxp vy cv cxp wss vu cv
      vv cv vx cv wbr vv wmo vu wal w3a vx vy c0 vb cv opelopabsb sylibr vx vy
      vv vu df-pbo syl6eleqr cA vb cv cop c0 vb cv cop cpbo eleq1 syl5ibr syl
      cA vb cv cpbo df-br syl6ibr cA c0 wceq cA cdm c0 cdm c0 cA c0 dmeq dm0
      syl6eq jctird alrimiv $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Two binary operations ` A , B ` on ` G ` are equal ( ` A = B ` ) if and
       only if ` dom A = dom B ` and ` A = B ` on ` dom A ` .

       Remark of [Bruck1971] p. 1 (Contributed by Richard Penner,
       29-Sep-2019.) $)
    eqpbo $p |- ( ( A PBO G /\ B PBO G ) -> ( A = B <-> ( dom A = dom B /\ A. x e. dom A ( A ` x ) = ( B ` x ) ) ) ) $=
      cA cG cpbo wbr cA wfun cB wfun cA cB wceq cA cdm cB cdm wceq vx cv cA cfv
      vx cv cB cfv wceq vx cA cdm wral wa wb cB cG cpbo wbr cA cG cpbo wbr cA
      cvv wcel cG cvv wcel wa cG c0 wne cA cG cG cxp cG cxp wss cA wfun w3a wa
      cA wfun cA cG brpbo2 cA cvv wcel cG cvv wcel wa cG c0 wne cA cG cG cxp cG
      cxp wss cA wfun simpr3 sylbi cB cG cpbo wbr cB cvv wcel cG cvv wcel wa cG
      c0 wne cB cG cG cxp cG cxp wss cB wfun w3a wa cB wfun cB cG brpbo2 cB cvv
      wcel cG cvv wcel wa cG c0 wne cB cG cG cxp cG cxp wss cB wfun simpr3
      sylbi vx cA cB eqfunfv syl2an $.
  $}

$( We make the following conventions in connection with a binary operation ` A ` on ` G ` :

   Remark of [Bruck1971] p. 1
$)

  ${
    $( (1) If ` <. a , b >. ` is in ` dom A ` , we usually write the "product"
       ` ( a A b ) ` instead of ` ( A `` <. a , b >. ) ` .  See ~ df-ov .

       Remark of [Bruck1971] p. 1 (Contributed by Richard Penner,
       29-Sep-2019.) $)
    pbov $p |- ( ( A PBO B /\ <. a , b >. e. dom A ) -> ( a A b ) = ( A ` <. a , b >. ) ) $=
      va cv vb cv cA co va cv vb cv cop cA cfv wceq cA cB cpbo wbr va cv vb cv
      cop cA cdm wcel wa va cv vb cv cA df-ov a1i $.

  $}

$( (2) The statement " ` ( a A b ) ` is defined in ` G ` " means that
   ` <. a , b >. ` is in ` dom A ` .

   (3) The statement " ` a b = c ` in ` G ` " means ` <. a , b >. `
   is in ` dom A ` , ` c ` is in ` G ` and
   ` ( A `` <. a , b >. ) = c ` . It will be obvious from the
   context what operations are in question.

   Remark of [Bruck1971] p. 1
$)

$(
###############################################################################
                         BASIC ALGEBRAIC STRUCTURES
###############################################################################

An algebra, in the most general sense, is one or more sets and one
or more n-ary operations on that set. That's very general.

Here the set in question for algebraic struture ` A ` is usually ` ( Base `` A ) `
with ` ( +g `` A ) ` being the binary operation for one-operation
algebras ( so we can treat them the same, even if that binary
operation is not very akin to addition) and the addition operation
for rings, while ` ( .r `` A ) ` is used for ring/field multiplication.

$)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                   Partial Magmas
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

  A partial magma is a universal algebra with one (perhaps
  incompletely-defined) binary operation, which need not have any
  special conditions placed on it (other than the closure property
  common to binary operations). So it is very nearly the most basic
  type of algebra there can be. ( The null set with any operations
  or a set with only 0-ary or 1-ary operations are more basic, but
  because they can't relate elements, I will, like all sloppy
  authors, contend that they are _uninteresting_. ) - Richard Penner

  In [Bruck1971] and earlier works, these are called _halfgroupoids_
  which is not quantitatively correct and inconvinient in that
  groupoid is more commonly associated today with a entirely different
  concept in the theory of categories.
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                   Definition and basic properties
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c PMgm $.
  $c C_PM $.

  $( Extend class notation with the class of all partial (incompletely defined)
     magmas. $)
  cpmgm $a class PMgm $.
  $( Define subset of Partial Magma. $)
  cspmgm $a class C_PM $.

  ${
    pmgmidmo.1 $e |- ( u e. B /\ A. x e. B ( < u , x > e. dom .+ -> ( u .+ x ) = x ) ) $.
    pmgmidmo.2 $e |- ( u e. B /\ A. x e. B ( < x , u > e. dom .+ -> ( x .+ u ) = x ) ) $.
    pmgmidmo.3 $e |- ( v e. B /\ A. x e. B ( < v , x > e. dom .+ -> ( v .+ x ) = x ) ) $.
    pmgmidmo.4 $e |- ( v e. B /\ A. x e. B ( < x , v > e. dom .+ -> ( x .+ v ) = x ) ) $.
    $( If ` u ` and ` v ` are both candiates for two-sided identity elements of
       a partial magma, if they operate on each other they must be the same
       candidate.  This has an important specialization for full magmas as in
       ~ mgmidmo. $)
    pmgmidmo $p |- ( ( < v , u > e. dom \/ < u , v > e. dom .+ ) -> u = v ) $= ? $.
  $}

  ${

    $d b g x y $.
    $( Definition of a partial magma.  A partial magma is a non-empty set
       equipped with perhaps only partially-defined internal operation ( see
       ~ pmgmcl ).

       Based on definition halfgroupoid in [Bruck1971] p. 1. $)
    df-pmgm $a |- PMgm = { g | [. ( Base ` g ) / b ]. [. ( +g ` g ) / p ]. ( b =/= (/) /\ A. x e. b A. y e. b ( <. x , y >. e. dom p -> ( x p y ) e. b ) ) } $.

  $}

  ${
    ispmgm.b $e |- B = ( Base ` G ) $.
    ispmgm.p $e |- .+ = ( +g ` G ) $.
    $( The predicate "is a partial magma." $)
    ispmgm $p |- ( G e. PMgm <-> ( B =/= (/) /\ A. a e. B A. b e. B ( <. a , b >. e. dom .+ /\ ( a .+ b ) e. B ) ) ) $= ? $.

  $}

  ${
    ispmgm2.b $e |- B = ( Base ` G ) $.
    ispmgm2.p $e |- .+ = ( +g ` G ) |` ( B X. B ) $.
    ispmgm2.s $e |- S = dom .+ $.
    $( The predicate "is a partial magma." $)
    ispmgm2 $p |- ( G e. PMgm <-> ( B =/= (/) /\ .+ : S --> B ) ) $= ? $.

  $}

  ${
    ispmgm3.b $e |- B = ( Base ` G ) $.
    ispmgm3.p $e |- .+ = ( +g ` G ) |` ( B X. B ) $.
    $( A _halfgroupoid_ ` G ` is a system consisting of a non-empty set ` G `
       and a binary operation on ` G ` .

       Based on definition halfgroupoid in [Bruck1971] p. 1. $)
    ispmgm3 $p |- ( G e. PMgm <-> .+ PBO B ) $= ? $.

  $}

$( A (proper or improper) subset ` H ` of the halfgroupoid ` G `
   is a _subhalfgroupoid_ ` G ` such that ` a b = c ` in ` G `
   whenever ` a b = c ` in ` H ` .

   Definition subhalfgroupoid in [Bruck1971] p. 1.
$)

  ${

    $d b c g h $.
    $( Definition of a sub partial magma.  A sub partial magma is partial magma
       where the operation (restricted to the base set) is a subset of that of
       another partial magma.

       Based on definition subhalfgroupoid in [Bruck1971] p. 1. $)
    df-spmgm $a |- C_PM = { <. h , g >. | ( h e. PMgm /\ g e. PMgm /\ [. ( Base ` g ) / b ]. [. ( +g ` g ) / p ]. [. ( Base ` h ) / c ]. [. ( +g ` h ) / o ]. ( o |` ( c X. c ) ) C_ ( p |` ( b X. b ) ) ) } $.

  $}


  ${
    isspmgm.c $e |- S = ( Base ` H ) $.
    isspmgm.b $e |- B = ( Base ` G ) $.
    isspmgm.o $e |- .(+) = ( +g ` H ) $.
    isspmgm.p $e |- .+ = ( +g ` G ) $.
    $( Relationship of a ` C_PM ` . $)
    isspmgm $p ( H C_PM G <-> ( H e. PMgm /\ G e. PMgm /\ ( .(+) |` ( H X. H ) ) C_ ( .+ |` ( B X. B ) ) ) ) $= ? $.
  $}

  ${
    isspmgm2.c $e |- S = ( Base ` H ) $.
    isspmgm2.b $e |- B = ( Base ` G ) $.
    isspmgm2.o $e |- .(+) = ( +g ` H ) |` ( S X. S ) $.
    isspmgm2.p $e |- .+ = ( +g ` G ) |` ( B X. B ) $.
    $( Relationship of a ` C_PM ` . $)
    isspmgm2 $p ( H C_PM G <-> ( H e. PMgm /\ G e. PMgm /\ .(+) C_ .+ ) ) $= ? $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                   Magmas
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

  A magma is a universal algebra with one binary operation, which
  need not have any special conditions placed on it (other than the
  closure property common to binary operations).

  Thanks to Frederic Line, who back in 2004 worked out some proofs
  long before the 2015 introduction of general structures by Mario
  Carneiro.
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                   Definition and basic properties
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c MgmNEW $.
  $c MgmRP $.
  $c C_Mgm $.

  $( Extend class notation with the class of all magmas. $)
  cmgmNEW $a class MgmNEW $.
  $( Extend class notation with the class of all magmas. $)
  cmgm $a class MgmRP $.
  $( Extend class notation with the relation of submagmas to magmas. $)
  csmgm $a class C_Mgm $.

$( df-gsum can be used to map words to elements of a magma. See gsumval2a $)

$( mndcl proves a Mnd is closed under the binary operation, thus a magma. $)

  ${

    $d b g x y $.
    $( Definition of a magma.  A magma is a non-empty set equipped with a
       completely-defined internal operation ( see ~ mgmcl ).

       Based on definition groupoid in [Bruck1971] p. 1. $)
    df-mgmRP $a |- MgmRP = { g e. PMgm | [. ( Base ` g ) / b ]. [. ( +g ` g ) / p ]. A. x e. b A. y e. b ( <. x , y >. e. dom b /\ ( x p y ) e. b ) } $.

  $}

  ${

    $d b g x y $.
    $( Definition of a magma.  A magma is a set equipped with an everywhere
       defined internal operation ( see ~ mgmclNEW ). $)
    df-mgmNEW $a |- MgmNEW = { g | [. ( Base ` g ) / b ]. [. ( +g ` g ) / p ].
A. x e. b A. y e. b ( x p y ) e. b } $.
  $}

  ${
    $d u v y $.  $d u v x A $.  $d u v x B $.  $d u v x C $.  $d u v x F $.
    $( This lemma might be useful. $)
    dfmgm2lem1 $p |- ( A. x e. ( A X. B ) E! y e. C x F y <-> A. u e. A A. v e. B ( u F v ) e. C ) $=
        vx cv vy cv cF wbr vy cC wreu vu cv vv cv cF co cC wcel vx vu vv cA cB
        ? ralxp $.
  $}

  ${
    $( Definition of a magma. $)
    dfmgm2 $p |- MgmNEW = { g | [. ( Base ` g ) / b ]. [. ( +g ` g ) / p ].
( p |` ( b X. b ) ) : ( b X. b ) --> b } $= ? $.
  $}

  ${
    ismgmRP.b $e |- B = ( Base ` G ) $.
    ismgmRP.p $e |- .+ = ( +g ` G ) $.
    $( The predicate "is a magma." $)
    ismgmRP $p |- ( G e. MgmRP <-> ( B =/= (/) /\ A. a e. B A. b e. B ( <. a , b >. e. dom .+ /\ ( a .+ b ) e. B ) ) ) $= ? $.

  $}

  ${
    ismgm2.b $e |- B = ( Base ` G ) $.
    ismgm2.p $e |- .+ = ( +g ` G ) |` ( B X. B ) $.
    $( The predicate "is a magma." $)
    ismgm2 $p |- ( G e. MgmRP <-> ( B =/= (/) /\ .+ : ( B X. B ) --> B ) ) $= ? $.
  $}

  ${
    ismgm3.b $e |- B = ( Base ` G ) $.
    ismgm3.p $e |- .+ = ( +g ` G ) $.
    $( A _groupoid_ ` G ` is a halfgroupoid such that ` a b ` is defined in
       ` G ` for all ` a , b ` in ` G ` .

       Based on definition groupoid in [Bruck1971] p. 1. $)
    ismgm3 $p |- ( G e. MgmRP <-> ( G e. PMgm /\ ( B X. B ) C_ dom .+ ) ) $= ? $.

  $}

  ${
    ismgm4.b $e |- B = ( Base ` G ) $.
    ismgm4.p $e |- .+ = ( +g ` G ) $.
    $( A _groupoid_ ` G ` is a halfgroupoid such that ` a b ` is defined in
       ` G ` for all ` a , b ` in ` G ` .

       Based on definition groupoid in [Bruck1971] p. 1. $)
    ismgm4 $p |- ( G e. MgmRP <-> ( G e. PMgm /\ A. a e. B A. b e. B <. a , b >. e. dom .+ ) ) $= ? $.

  $}

  ${

    $d a b g v p B $.  $d a b g v p G $.  $d a b g v p .+ $.
    ismgmNEW.g $e |- G e. _V $.
    ismgmNEW.b $e |- B = ( Base ` G ) $.
    ismgmNEW.p $e |- .+ = ( +g ` G ) $.
    $( The predicate "is a magma."  (Contributed by Richard Penner,
       21-Sep-2019.) $)
    ismgmNEW $p |- ( G e. MgmNEW <-> A. a e. B A. b e. B ( a .+ b ) e. B ) $=
      cG cmgmNEW wcel cG va cv vb cv vp cv co vv cv wcel vb vv cv wral va vv cv
      wral vp vg cv cplusg cfv wsbc vv vg cv cbs cfv wsbc vg cab wcel va cv vb
      cv c.pl co cB wcel vb cB wral va cB wral cmgmNEW va cv vb cv vp cv co vv
      cv wcel vb vv cv wral va vv cv wral vp vg cv cplusg cfv wsbc vv vg cv cbs
      cfv wsbc vg cab cG va vb vg vp vv df-mgmNEW eleq2i va cv vb cv vp cv co
      vv cv wcel vb vv cv wral va vv cv wral vp vg cv cplusg cfv wsbc vv vg cv
      cbs cfv wsbc va cv vb cv c.pl co cB wcel vb cB wral va cB wral vg cG cG
      cvv wcel va cv vb cv c.pl co cB wcel vb cB wral va cB wral cG cvv
      ismgmNEW.g elexi a1i vg cv cG wceq va cv vb cv vp cv co vv cv wcel vb vv
      cv wral va vv cv wral vp vg cv cplusg cfv wsbc va cv vb cv c.pl co cB
      wcel vb cB wral va cB wral vv vg cv cbs cfv cB cvv vg cv cbs cfv cvv wcel
      vg cv cG wceq vg cv cbs fvex a1i vg cv cG wceq vg cv cbs cfv cG cbs cfv
      cB vg cv cG cbs fveq2 ismgmNEW.b syl6eqr vg cv cG wceq vv cv cB wceq wa
      va cv vb cv vp cv co vv cv wcel vb vv cv wral va vv cv wral va cv vb cv
      c.pl co cB wcel vb cB wral va cB wral vp vg cv cplusg cfv c.pl cvv vg cv
      cplusg cfv cvv wcel vg cv cG wceq vv cv cB wceq wa vg cv cplusg fvex a1i
      vg cv cG wceq vv cv cB wceq wa vg cv cplusg cfv cG cplusg cfv c.pl vg cv
      cG wceq vv cv cB wceq wa vg cv cG cplusg vg cv cG wceq vv cv cB wceq
      simpl fveq2d ismgmNEW.p syl6eqr vg cv cG wceq vv cv cB wceq wa vp cv c.pl
      wceq wa va cv vb cv vp cv co vv cv wcel vb vv cv wral va cv vb cv c.pl co
      cB wcel vb cB wral va vv cv cB vg cv cG wceq vv cv cB wceq vp cv c.pl
      wceq simplr vg cv cG wceq vv cv cB wceq wa vp cv c.pl wceq wa va cv vb cv
      vp cv co vv cv wcel va cv vb cv c.pl co cB wcel vb vv cv cB vg cv cG wceq
      vv cv cB wceq vp cv c.pl wceq simplr vg cv cG wceq vv cv cB wceq wa vp cv
      c.pl wceq wa va cv vb cv vp cv co va cv vb cv c.pl co vv cv cB vg cv cG
      wceq vv cv cB wceq wa vp cv c.pl wceq wa vp cv c.pl va cv vb cv vg cv cG
      wceq vv cv cB wceq wa vp cv c.pl wceq simpr oveqd vg cv cG wceq vv cv cB
      wceq vp cv c.pl wceq simplr eleq12d raleqbidv raleqbidv sbcied2 sbcied2
      elab3 bitri $.

  $}

  $(
    If necessary move ~ mgmidmo earlier than here.
    ` |- E* u e. B A. x e. B ( ( u .+ x ) = x /\ ( x .+ u ) = x ) `
  $)

  ${
    $d a b B $.  $d a b G $.  $d a b .+ $.  $d a b X $.  $d b Y $.
    mgmclNEW.g $e |- G e. _V $.
    mgmclNEW.b $e |- B = ( Base ` G ) $.
    mgmclNEW.p $e |- .+ = ( +g ` G ) $.
    $( Closure of the operation of a magma.  (Contributed by Richard Penner,
       22-Sep-2019.) $)
    mgmclNEW $p |- ( ( G e. MgmNEW /\ X e. B /\ Y e. B ) -> ( X .+ Y ) e. B ) $=
      cG cmgmNEW wcel cX cB wcel cY cB wcel cX cY c.pl co cB wcel cG cmgmNEW
      wcel va cv vb cv c.pl co cB wcel vb cB wral va cB wral cX cB wcel cY cB
      wcel wa cX cY c.pl co cB wcel cG cmgmNEW wcel va cv vb cv c.pl co cB wcel
      vb cB wral va cB wral cB c.pl cG va vb mgmclNEW.g mgmclNEW.b mgmclNEW.p
      ismgmNEW biimpi va cv vb cv c.pl co cB wcel cX cY c.pl co cB wcel cX vb
      cv c.pl co cB wcel va vb cX cY cB cB va cv cX wceq va cv vb cv c.pl co cX
      vb cv c.pl co cB va cv cX vb cv c.pl oveq1 eleq1d vb cv cY wceq cX vb cv
      c.pl co cX cY c.pl co cB vb cv cY cX c.pl oveq2 eleq1d rspc2v mpan9 3impb
      $.

  $}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                   Monoids (additional)
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                   Definition and basic properties (additional)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${

    $( A monoid is a magma. $)
    mndmgm $p |- ( G e. Mnd -> G e. MgmNEW ) $= ? $.

  $}
