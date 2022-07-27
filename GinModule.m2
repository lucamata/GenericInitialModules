-- -*- coding: utf-8 -*-
newPackage(
        "GinModule",
        Version => "1.0", 
        Date => "October 2, 2019",
        Authors => {{Name => "Luca Amata", Email => "lamata@unime.it", HomePage => "mat521.unime.it/amata"}},
        Headline => "A Macaulay2 package for computing the generic initial module of a graded submodule of a finitely generated free module",
        DebuggingMode => false
        )

export {
"initialDegree", "gins", "gin", "initialModule", "isMonomialModule", "getIdeals", "isBorelModule", "minimalBettiNumbers",

--pvt

--options
"AllModules"
}

------------------------------------------------------------------------
-- compute the initial degree of a graded ideal
------------------------------------------------------------------------
initialDegree = method(TypicalValue=>ZZ)
initialDegree Module := M -> (
    if isHomogeneous M then return min flatten degrees image mingens M
    else error "expected a graded module";
    )                             

------------------------------------------------------------------------
-- compute a family of generic initial modules of a graded submodule
------------------------------------------------------------------------    
gins = method(TypicalValue => List)
gins (Module,ZZ,ZZ) := (M,it,cmp) -> (
    F := ambient M;
    S := ring M;
    G := new MutableList from {};
    it=abs it;
    cmp=abs cmp;

    for i in (0..it-1) do (
        N:=M;
        for j in (0..cmp-1) do (
            setRandomSeed random currentTime();
            RMS := map(S, S, random(S^{0}, S^{numgens S:-1}));
            RMF := map(F, F, random(F, F));
            while rank RMF< rank F do
                RMF = map(F, F, random(F, F));
    
            N=image(RMF*(gens RMS N));
        );
        gM:=image monomials leadTerm gens gb N;
    
        if number(G,x->x_0==gM)==0 then G=join(G,{(gM,1)})
        else (
            pos:=position(toList G,x->x_0==gM); 
            G#pos=(gM,(G#pos)_1+1);
        );
    );     
    
    toList G    
)   
    
------------------------------------------------------------------------
-- compute the generic initial module of a graded submodule
------------------------------------------------------------------------    
gin = method(TypicalValue => Module)
gin Module := M -> (
    G:=gins(M,30,2); 
    m:=max (G / (x->x_1));
    p:=positions(G,x->x_1==m);
    if #p>1 then return null;       
    
    G_(p_0)_0   
)   
    
-------------------------------------------------------------------------------------------
-- compute the initial module of a module
----------------------------------------------------------------------------------------------
initialModule = method(TypicalValue=>Module)
initialModule Module := M -> image monomials leadTerm gens gb M

-------------------------------------------------------------------------------------------
-- whether a module is monomial
----------------------------------------------------------------------------------------------
isMonomialModule = method(TypicalValue=>Boolean)
isMonomialModule Module := M -> initialModule M == M
  
------------------------------------------------------------------------
-- get ideals from a module
------------------------------------------------------------------------
getIdeals = method(TypicalValue=>List)
getIdeals Module := M -> (
    S:=ring M;
    F:=ambient M;
    rk:=rank F;
    I:={};
    
    if isMonomialModule M then (
       ListI:=entries compress mingens M;
       r:=#ListI;

       for k from 0 to r-1 do (
          gen:=rsort unique select(ListI#k,x->x!=0);
          if gen=={} then gen={0_S};       
          I=append(I,ideal gen);
       );
       for k from r to rk-1 do (
          I=append(I,ideal(0_S))
       );
    ) else error "expected a monomial module";
    I
)  

----------------------------------------------------------------------------
-- whether a monomial module is Borel fixed
----------------------------------------------------------------------------
isBorelModule = method(TypicalValue=>Boolean)
isBorelModule Module := M -> (
    --if not isMonomialModule M then return false;
    S:=ring M;
    F:=ambient M;   
    m:=ideal vars S;     
    r:=rank F;
    I:=getIdeals M;  -- if M is not monomial the procedure stops

    for k from 0 to r-1 do       
        if not isBorel monomialIdeal I#k then return false;

        for k from 1 to r-1 do (
            esp:=(degree(F_k))#0-(degree(F_(k-1)))#0;        
            idCond:=rsort unique flatten entries compress mingens m^(esp);    
            if idCond=={} then idCond={0_S};          
            left:=(ideal idCond)*I#k;
            if not(isSubset(left,I#(k-1))) then return false;
        );
   
    true
)   
  
-------------------------------------------------------------------------------------------
-- returns the minimal Betti numbers of a Module
----------------------------------------------------------------------------------------------
minimalBettiNumbers = method(TypicalValue=>BettiTally)
minimalBettiNumbers Module := M -> betti res image mingens M
    


beginDocumentation()
-------------------------------------------------------
--DOCUMENTATION ExteriorIdeals
-------------------------------------------------------

document {
     Key => {GinModule},
     Headline => "A package for computing the generic initial module of a graded submodule of a finitely generated free module",
     TT "GinModule is a package for computing the generic initial module of a graded submodule of a finitely generated free module",
     PARA {"Other acknowledgements:"},
        "Some ideas was taken from the package RandomIdeals, which is available at ",
        HREF{"http://www2.macaulay2.com/Macaulay2/doc/Macaulay2-1.11/share/doc/Macaulay2/RandomIdeals/html/","RandomIdeals"},     
     }

document {
     Key => {initialDegree,(initialDegree,Module)},
     Headline => "returns the initial degree of a graded module",
     Usage => "initialDegree M",
     Inputs => {"M" => {"a graded module"}
      },
     Outputs => {ZZ => {"representing the initial degree of the module ", TT "M"}},
     "The initial degree of a graded module ", TT "M", " is the least degree of a homogeneous generator of " , TT "M",
     PARA {"Example:"},
     EXAMPLE lines ///
         S=QQ[x_1..x_4]
         initialDegree image matrix{{x_1*x_2,x_2*x_3*x_4}}
         initialDegree image matrix{{x_1*x_3*x_4}}
      ///
     }

document {
     Key => {isBorelModule,(isBorelModule,Module)},
     Headline => "whether a module is Borel fixed",
     Usage => "isBorelModule M",
     Inputs => {"M" => {"a monomial submodule of a finitely generated free module"}
      },
     Outputs => {Boolean => {"true whether module ", TT "M", " is Borel fixed"}},     
     PARA {"Examples:"},
     EXAMPLE lines ///
           S=QQ[x_1..x_4]
           isBorelModule image {x_1*x_2,x_2*x_3}
           isBorelModule image {x_1*x_2,x_1*x_3,x_1*x_4,x_2*x_3}
     ///,
     SeeAlso =>{gin},
     }

document {
     Key => {initialModule,(initialModule,Module)},
     Headline => "returns the initial module of a module M",
     Usage => "initialModule M",
     Inputs => {"M" => {"a graded submodule of a finitely generated free module"}
      },
     Outputs => {Module => {"the initial module of the module ", TT "M", " with default monomial order"}},
     PARA {"Example:"},
     EXAMPLE lines ///
           S=QQ[x_1..x_5]
           M=image {x_1*x_2+x_3*x_4*x_5,x_1*x_3+x_4*x_5,x_2*x_3*x_4}
           initialModule M
      ///
     }
     
document {
     Key => {minimalBettiNumbers,(minimalBettiNumbers,Module)},
     Headline => "returns the minimal Betti numbers of a module M",
     Usage => "minimalBettiNumbers M",
     Inputs => {"M" => {"a graded submodule of a finitely generated free module"}
      },
     Outputs => {BettiTally => {"the Betti table of the module ", TT "M", " computed using its minimal generators"}},
     PARA {"Example:"},
     EXAMPLE lines ///
           S=QQ[x_1..x_4]
           M=image matrix{x_1*x_2,x_1*x_3,x_2*x_3}
           N=image matrix{join(flatten entries gens I,{x_1*x_2*x_3})}
           M==N
           betti res M==betti res N
           minimalBettiNumbers M==minimalBettiNumbers N
      ///
     }


------------------------------------------------------------
-- DOCUMENTATION FOR OPTION
------------------------------------------------------------

----------------------------------
-- Shift (for macaulayExpansion)
----------------------------------

--document {
--     Key => {AllModules,
--    [gin,AllModules]},
--     Headline => "optional argument for gin",
--     "Whether it is true the function gin gives the monomials modules found by some transformations applied to ", TT "M.", "The most frequent is the gin of ", TT "M."
--     SeeAlso =>{gin} 
--     }


------------------------------------------------------------
-- TESTS
------------------------------------------------------------

----------------------------
-- Test minimalBettiNumbers
----------------------------
TEST ///
S=QQ[x_1..x_4]
I=ideal {x_1*x_2,x_1*x_3,x_2*x_3}
J=ideal(join(flatten entries gens I,{x_1*x_2*x_3}))
assert(I==J)
assert(minimalBettiNumbers I==minimalBettiNumbers J)
///

----------------------------
-- Test initialModule
----------------------------
TEST ///
S=QQ[x_1..x_5]
M=image matrix{{x_1*x_2+x_3*x_4*x_5,x_1*x_3+x_4*x_5,x_2*x_3*x_4}}
N=image matrix{{x_1*x_2,x_1*x_3,x_1*x_4*x_5,x_2*x_3*x_4,x_2*x_4*x_5,x_3*x_4*x_5}}
assert(M!=N)
///

end

restart
installPackage ("GinModule", UserMode=>true)
loadPackage "GinModule"
viewHelp