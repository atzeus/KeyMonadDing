\documentclass[preprint]{sigplanconf}
%include polycode.fmt
\usepackage{amsthm}
\usepackage{amssymb}
\usepackage{relsize}
\usepackage[a]{esvect}
\usepackage{marvosym}
\usepackage{graphicx}
\usepackage{url}
\usepackage{wasysym}
\usepackage{multirow}
\usepackage{array}
\newcolumntype{L}[1]{>{\raggedright\let\newline\\\arraybackslash\hspace{0pt}}m{#1}}
\newcolumntype{C}[1]{>{\centering\let\newline\\\arraybackslash\hspace{0pt}}m{#1}}
\newcolumntype{R}[1]{>{\raggedleft\let\newline\\\arraybackslash\hspace{0pt}}m{#1}}


\newcommand{\app}{\mathbin{<\!\!\!\!\mkern1.4mu\raisebox{-1.55pt}{\scalebox{0.9}{*}}\mkern1.4mu\!\!\!\!>}}
\newcommand{\aplus}{\mathbin{<\!\!\!\!\mkern1.4mu +\mkern1.4mu\!\!\!\!>}}
\newcommand{\fmap}{\mathbin{<\!\!\!\mkern-0.4mu\raisebox{0.0pt}{\scalebox{0.8}{\$}}\mkern-0.4mu\!\!\!>}}
%format :~: =  ":\sim:"
%format :++: =  ":\!\!+\!\!\!+\!\!:"
%format `Sub` = "\subseteq"
%format forall = "\forall"
%format exists = "\exists"
%format . = ".\:"
%format >>> = "\mathbin{>\!\!\!>\!\!\!>}"
%format .>>= = "\cdot\!\!\!\bind"
%format .>> = "\cdot\!\!>\!\!\!>"
%format getr = "!\:r"
%format -< = "\prec"
%format >- = "\succ"
%format ~ = "\:\sim\:"
%format :. = "\circ"
%format procb = "\mathbf{proc}"
%format <$ = "\cmap"
%format <*> = "\app"
%format <$> = "\fmap"
%format <+> = "\aplus"
%format E1 = "E_1"
%format E2 = "E_2"
%format EN = "E_n"
%format uncurryn = "\mathit{uncurry}_n"
\title{The Key Monad:\\Type-Safe Unconstrained Dynamic Typing}
\authorinfo{Atze van der Ploeg \and Koen Claessen}{Chalmers University of Technology}
           {\{atze, koen\}@@chalmers.se}
\authorinfo{Pablo Buiras}{Harvard University}{pbuiras@@seas.harvard.edu}
\begin{document}
\maketitle
\newcommand{\api}{\textsc{api}}
\newcommand{\gadt}{\textsc{gadt}}
\newcommand{\ghc}{\textsc{ghc}}
\newcommand{\hoas}{\textsc{hoas}}
\newcommand{\st}{\textsc{st}}
\newcommand{\atze}[1]{{\it Atze says: #1}}
\newcommand{\koen}[1]{{\it Koen says: #1}}
\newcommand{\pablo}[1]{{\it Pablo says: #1}}


\begin{abstract}
\pablo{To discuss: There are grammatical errors in this abstract that
  I believe I have fixed but
  were rolled back. The same mistakes occur in other places in the
  paper when listing the things we could 'otherwise not do'.}
 We present a small extension to Haskell (+ \gadt s and rank-2 types) called the
  Key monad. With the Key monad, unique keys of different types can be
  created and can be tested for equality. When two keys are equal, we
  obtain a proof that their types are equal. This gives us a form of
  dynamic typing, without the need for |Typeable| constraints. We
  show that this extension allows us to safely do things we could not
  otherwise do, namely: implement the \st{} monad, implement an
  embedded form of arrow notation in Haskell and translate
  parametric \hoas{} to typed de Bruijn indices, among others. Although strongly
  related to the \st{} monad, the Key monad is simpler and might be 
  easier to prove safe. We do not provide such a proof of the safety of the Key monad, but we note that, surprisingly, a full proof of the safety of
  the \st{} monad remains elusive to this day. Hence, another reason for
  studying the Key monad is that a safety proof for it might
  be a stepping stone towards a safety proof of the \st{} monad as well.
\end{abstract}


\section{Introduction}

The \st{} monad \cite{stmonad} in Haskell is an impressive feat of language design, but also a complicated beast. It provides and combines three separate features: (1) an abstraction for {\em global memory references} that can be efficiently written to and read from, (2) a mechanism for embedding computations involving these memory references in {\em pure computations}, and (3) a design that allows references in the same computation to be of {\em arbitrary, different types}, in a type-safe manner.

\begin{figure}[t]
\rule{\columnwidth}{0.4pt}
\begin{code}
type KeyM s a
type Key s a

instance Monad (KeyM s)
newKey        :: KeyM s (Key s a)
testEquality  :: Key s a -> Key s b -> Maybe (a :~: b)
runKeyM       :: (forall s. KeyM s a) -> a

data a :~: b where Refl :: a :~: a
\end{code}
\caption{The Key monad interface}
\label{fig:key-monad}
\end{figure}

In this paper, we attempt to provide a new abstraction in Haskell that
embodies only feature (3) above: the combination of references (which we call {\em keys}) of different, unconstrained types in the same computation. The result is a small library called {\em the Key monad}. The \api{} is given in Fig.\ \ref{fig:key-monad}.

The Key monad |KeyM| is basically a crippled version of the \st{} monad: we can monadically create keys of type |Key s a| using the function |newKey|, but we cannot read or write values to these keys; in fact, keys do not carry any values at all. We can convert a computation in |KeyM| into a pure value by means of |runKeyM|, which requires the argument computation to be polymorphic in |s|, just like |runST| would.

The only new feature is the function |testEquality|, which compares two keys for equality. But the keys do not have to be of the same type! They just have to come from the same |KeyM| computation, indicated by the |s| argument. If two keys are not equal, the answer is |Nothing|. However, if two keys are found to be equal, {\em then their types should also be the same}, and the answer is |Just Refl|, where |Refl| is a constructor from the \gadt{} |a :~: b| that functions as the ``proof'' that |a| and |b| are in fact the same type\footnote{It is actually possible to add |testEquality| to the standard interface of |STRef|s, which would provide much the same features in the \st{} monad as the Key monad would, apart from some laziness issues. However, because of its simplicity, we think the Key monad is interesting in its own right.}.

Why is the Key monad interesting? There are two separate reasons.

First, decoupling the ability to combine different types into one computation from computations involving state allows programmers to use the Key monad in situations where the \st{} monad would not have been suitable. In fact, the bulk of this paper presents examples of uses of the Key monad that would have been impossible without |testEquality|.

Second, the Key monad is simpler than the \st{} monad, because it does not involve global references, or any updatable state at all. We would like to argue that therefore, the Key monad is easier to understand than the \st{} monad. Moreover, given the Key monad, the \st{} monad is actually implementable in plain Haskell, albeit in a less time- and memory-efficient way than the original \st{} monad (that is, missing feature (1) above, but still providing features (2) and (3)).
The second reason comes with a possibly unexpected twist.

After its introduction in 1994, several papers have claimed to establish the safety, fully or partially, of the \st{} monad in Haskell \cite{stmonad,LaunchburySabry,AriolaSabry,MoggiSabry}. By safety we mean three things: (a) type safety (programs using the \st{} monad are still type safe), (b) referential transparency (programs using the \st{} monad are still referentially transparent), and (c) abstraction safety (programs using the \st{} monad still obey the parametricity theorem). It came as a complete surprise to the authors that {\em none of the papers we came across in our literature study actually establishes the safety of the \st{} monad in Haskell!}

So, there is a third reason for studying the Key monad: A safety proof for the Key monad could be much simpler than a safety proof for the \st{} monad. The existence of such a proof would conceivably lead to a safety proof of the \st{} monad as well; in fact this is the route that we would currently recommend for anyone trying to prove the \st{} monad safe.

This paper does not provide a formal safety proof of the Key monad. Instead, we will argue that the safety of the Key monad is just as plausible as the safety of the \st{} monad. We hope that the reader will not hold it against us that we do not provide a safety proof. Instead, we would like this paper to double as a call to arms, to find (ideally, mechanized) proofs of safety of both the Key monad and the \st{} monad!

Our contributions are as follows:
\begin{itemize}
\item We present the Key monad (Section \ref{keym}) and argue for its safety (Section \ref{safety}).
\item We show that added power of the Key monad allows us to do things we cannot do without it, namely:
     \begin{itemize}
          \item Implement the \st{} monad (Section \ref{keym}).
          \item Implement an \emph{embedded} form of arrow notation (Section \ref{arrow}).
          \item Represent typed variables in typed representations of syntax (Section \ref{syntax}).
          \item Translate parametric \hoas{} to nested de Bruijn indices, which allows interpretations of parametric \hoas{} terms, such translation to Cartesian closed categories, which are not possible otherwise (Section \ref{syntax}).
\end{itemize}
\item We present an argument why the Key monad is not expressible in Haskell (without |unsafeCoerce|) (Section \ref{impl}).
\end{itemize}
We discuss the state of the proof of the safety of the \st{} monad in section \ref{stdis} and we conclude in Section \ref{conc}.

The Haskell code discussed in this paper can be found online at: 
\url{https://github.com/koengit/KeyMonad}

\section{The Key monad}
\label{keym}

In this section, we describe the Key monad, what it gives us, and its relation to the \st{} monad.

The interface of the Key monad (Fig.\ \ref{fig:key-monad}) features two abstract types (i.e., types with no user-accessible constructors): |Key| and |KeyM|. The Key monad gives the user the power to create a new, unique value of type |Key s a| via |newKey|. The only operation that is supported on the type |Key| is |testEquality|, which checks if two given keys are the same, and if they are it returns a ``proof'' that the types associated with the names are the \emph{same} types. 

\subsection{Unconstrained dynamic typing}

The power to prove that two types are the same allows us to do similar things as with |Data.Typeable|, but \emph{without} the need for |Typeable| constraints. For instance, we can create a variant of |Dynamic| using |Key|s instead of type representations. When given a key and value, we can ``lock up'' the value in a box, which, like |Dynamic|, hides the type of its contents.
\begin{code}
data Box s where
  Lock :: Key s a -> a -> Box s
\end{code} If we have a |Key| and a |Box|, we can try to unlock to the box to recover the value it contains.
\begin{code}
unlock :: Key s a -> Box s -> Maybe a
unlock k (Lock k' x) =
   case testEquality k k' of
    Just Refl  -> Just x
    Nothing    -> Nothing
\end{code}
If we used the right key, we get |Just| the value in the box, and we get |Nothing| otherwise.

We can use |Box|es to create a kind of \emph{heterogeneous maps}: a data structure that that maps keys to values of the type corresponding to the key. The interesting feature here is that the type of these heterogenous maps does not depend on the types of the values that are stored in it, nor do the functions have |Typeable| constraints. We can implement such maps straightforwardly as follows\footnote{For simplicity, this is a rather inefficient implementation, but a more efficient implementation (using |IntMap|s) can be given if we add a slightly unsafe function |hashKey :: Key s a -> Int| to the Key monad.}:
\begin{code}
newtype KeyMap s = Km [Box s]

empty :: KeyMap s
empty = Km []

insert :: Key s a -> a -> KeyMap s -> KeyMap s
insert k v (Km l) = Km (Lock k v : l)	

lookup :: Key s a -> KeyMap s -> Maybe a
lookup k (Km [])       = Nothing
lookup k (Km (h : t))  = 
  unlock k h `mplus` lookup k (Km t)

\end{code}

\subsection{Implementing the \st{} monad}

Armed with our newly obtained |KeyMap|s, we can implement an (inefficient) version of the \st{} monad as follows. The implementation of |STRef|s is simply as an alias for |Key|s:
\begin{code}
type STRef s a = Key s a
\end{code}
We can now use the Key monad to create new keys, and use a |KeyMap| to represent the current state of all created |STRef|s.
\begin{code}
newtype ST s a =
     ST (StateT (KeyMap s) (KeyM s) a)
  deriving (Functor,Applicative,Monad)
\end{code}
It is now straightforward to implement the operations for |STRef|s:
\begin{code}
newSTRef :: a -> ST s (STRef s a)
newSTRef v = ST $ 
  do  k <- lift newKey
      modify (insert k v)
      return k

readSTRef :: STRef s   a -> ST s a
readSTRef r = ST $ (getr) <$> get

writeSTRef :: STRef s a -> a -> ST s ()
writeSTRef k v = ST $ modify (insert k v)


\end{code}
Finally, the implementation of |runST| simply runs the monadic computation contained in the \st{} type:
\begin{code}
runST :: (forall s. ST s a) -> a
runST m = runKeyM (evalStateT (unpack m) empty)

unpack ::  (forall s. ST s a) -> 
           (forall s. StateT (KeyMap s) (KeyM s) a)
unpack (ST m) = m
\end{code}

\subsection{Implementing the Key monad with the \st{} monad}

Note that while the Key monad can be used to implement the \st{} monad, the converse is not true. The problem is that there is no function:
\begin{code}
testEquality ::  STRef s a -> STRef s b -> 
                 Maybe (a :~: b)
\end{code}
It is straightforward to implement this function using |unsafeCoerce|:
\begin{code}
testEquality x y
   | x == unsafeCoerce y  = Just (unsafeCoerce Refl)
   | otherwise            = Nothing
\end{code}
The |unsafeCoerce| in |x == unsafeCoerce y| is needed because the types of the references might not be the same. Hence, another way to think of this paper is that we claim that the above function is \emph{safe}, that this allows us to do things which we could not do before, and that we propose this as an extension of the \st{} monad library. 

Why is this function safe? The reason is that if two references are the same, then their types must also be the same. This invariant must already be true for \st{} references, because otherwise we could have two references pointing to the same location with different types. Writing to one references and then reading for the other would coerce the value from one type to another! Hence, yet another way of thinking of the Key monad is that it splits reasoning based on this invariant into a separate interface and makes it available to the user via |testEquality|.

In the same line of reasoning, it is already possible to implement a similar, but weaker, version of |testEquality| using only the standard \st{} monad functions. If we represent keys of type |Key s a| as a pair of an identifier and an |STRef|s containing values of type |a|, then we can create a function that casts a value of type |a| to |b|, albeit monadically.
\begin{code}
data Key s a = Key{  ident :: STRef s (),
                     ref   :: STRef s a }

newKey :: ST s (Key s a)
newKey = Key <$> newSTRef undefined <*> newSTRef undefined

testEqualityM ::  Key s a -> Key s b -> 
                  Maybe (a -> ST s b)
testEqualityM ka kb
  |  ident ka /= ident kb  = Nothing
  |  otherwise             = Just $ \x ->
       do  writeSTRef (ref ka) x
           readSTRef (ref kb)
\end{code} 
This implementation, although a bit brittle because it relies on strong invariants, makes use of the insight that if the two references are actually the same reference, then writing to one reference must trigger a result in the other.

Note that with this |testEquality| function for |STRef|s it is possible to implement the Key monad, but the our implementation of the Key monad is more lazy. In particular, using the above implementation of |testEquality|, following holds for the (lazy) \st{} monad:
\begin{code} 
(runST $ undefined >> newSTRef 4 >>= 
  \x -> return (testEquality x x)) == undefined
\end{code}
For our implementation of the Key monad the following holds:
\begin{code}
(runKeyM $ undefined >> newKey >>=
   \x -> return (testEquality x x)) == Just Refl
\end{code}

\subsection{Relation to |Typeable|}

The {\tt base} library |Data.Typeable| provides similar functionality to the Key monad. Typeable is a type class that provides a value-level representation of the types that implement it. In fact, since version 4.7 of {\tt base}, it provides a function
\begin{code}
eqT :: forall a b. (Typeable a, Typeable b) => Maybe (a :~: b)
\end{code}
where |(:~:)| is the \gadt{} from Figure \ref{fig:key-monad}. This function gives |Just Refl| if both \emph{types} are the same, whereas |testEquality| from the Key monad only gives |Just Refl| if the \emph{keys} are the same. If we have two keys with the same type, but which originate from different |newKey| invocations, the result of |testEquality| will be |Nothing|. 

Another difference is that with the Key monad, to obtain a key for a type |a|, we do not need a constraint on the type |a|, which we do need to get a value-level type representation using |Typeable|. These constraints can leak to the user-level interface. For example, we can also implement a variant of the \st{} monad using |Typeable|, by storing in each |STRef| a unique number and a representation of its type. We will then need to change the interface such that we have access to the value-level type representations, by adding |Typeable| constraints. For example, the type of |newSTRef| then becomes
\begin{code}
newSTRef :: Typeable a => a -> ST s (STRef s a)
\end{code}
In fact, all example usages of the Key monad in this paper can also be implemented by using |Typeable| and unique numbers and adding constraints to the user interface. We could even implement the Key monad itself by adding a |Typeable| constraint to |newKey|. However, using the Key monad has the benefit that it is \emph{unconstrained}: we can use it even when |Typeable| dictionaries are unavailable.

\subsection{Key monad laws}

Informally, the Key monad allows us to create new keys and compare them, maybe obtaining a proof of the equality of their associated types. To give a more precise specification and to allow equational reasoning, we also present the Key monad laws shown in Figure \ref{laws}, which we will now briefly discuss. The |sameKey| and |distinctKey| laws describe the behavior of |testEquality|.

\begin{figure}
\hspace{-0.7cm}
\begin{tabular}{ r  c  l r}
\begin{minipage}{0.42\columnwidth}
\begin{code}
do  k <- newKey 
    f (testEquality k k)
\end{code}
\end{minipage}& |=| & \hspace{-0.5cm}\begin{minipage}{0.3\columnwidth}
\begin{code}
do  k <- newKey 
    f (Just Refl)
\end{code}
\end{minipage}& (|sameKey|) \\[-0.2cm]
\begin{minipage}{0.42\columnwidth}
\begin{code}
do  k <- newKey 
    l <- newKey
    f (testEquality k l)
\end{code}
\end{minipage}&  |=| & \hspace{-0.5cm}\begin{minipage}{0.3\columnwidth}
\begin{code}
do  k <- newKey 
    l <- newKey
    f Nothing
\end{code}
\end{minipage}& (|distinctKey|) \\[-0.2cm] \begin{minipage}{0.22\columnwidth}
\begin{code}
do  x <- f
    y <- g
    h x y
\end{code}
\end{minipage}
 &  |=| & \hspace{-0.5cm}\begin{minipage}{0.2\columnwidth}
\begin{code}
do  y <- g
    x <- f
    h x y
\end{code}
\end{minipage}
& (|commutative|) \\[-0.2cm]
\begin{minipage}{0.15\columnwidth} \begin{code}m >> n\end{code}\end{minipage} & |=| & \hspace{-0.5cm}\begin{minipage}{0.1\columnwidth} \begin{code} n\end{code} \end{minipage} & (|purity|)  \\[-0.2cm]
\begin{minipage}{0.35\columnwidth} \begin{code} runKey (return x) \end{code}\end{minipage}& |=| &\hspace{-0.55cm} \begin{minipage}{0.1\columnwidth} \begin{code}x\end{code} \end{minipage} & (|runReturn|) \\[-0.2cm]
\begin{minipage}{0.35\columnwidth} \begin{code} runKey (f <$> m)\end{code} \end{minipage}  & |=| & \hspace{-0.5cm}\begin{minipage}{0.3\columnwidth} \begin{code}f (runKey m)\end{code}\end{minipage} & (|runF|) \\[-0.15cm]
\multicolumn{3}{c}{(if |m :: forall s. KeyM s a|)} & 
\end{tabular}
\caption{Key monad laws}
\label{laws}
\end{figure}

The |commutative| law states that the Key monad is a commutative monad: the order of actions does not matter. The |purity| law might be a bit surprising: it states that doing some Key computation and then throwing away the result is the same as not doing anything at all! The reason for this is that the only property of each key is that it is distinct from all other keys: making keys and then throwing them away has no (observable) effect on the rest of the computation.

The last two laws, |runReturn| and |runF|,  state how we can get the values out of a |KeyM| computation with |runKey|. The |runF| law states that we can lazily get the results of a (potentially) infinite |KeyM| computation. The side condition that |m| has type |forall s. KeyM s a| (for some type |a|) rules out wrong specialization of the law, such as:  
\begin{code}
runKey (f <$> newKey) = f (runKey newKey)
\end{code}
This specialization does \emph{not} hold because, the left hand side type-checks, but the right hand side does not: the ``s'' would escape. 



\section{Embedding Arrow notation}
\label{arrow}
\begin{figure}
  \rule{\columnwidth}{0.4pt}
\begin{code}
class Arrow a where
  arr    :: (x -> y) -> a x y
  (>>>)  :: a x y -> a y z -> a x z
  first  :: a x y -> a (x,z) (y,z)
  second :: a x y -> a (z,x) (z,y)
  second x = flip >>> first x >>> flip
    where flip  = arr (\(x,y) -> (y,x))
\end{code}
\caption{The  arrow type class.}
\label{arrowsdef}
\end{figure}

In this section, we show that the Key monad gives us the power to implement an \emph{embedded} form of \emph{arrow syntax}. Without the Key monad, such syntax is, as far as we know, only possible by using specialized compiler support.

\subsection{Arrows vs Monads}

The |Arrow| type class, shown in Figure~\ref{arrowsdef}, was introduced by Hughes~\cite{arrows} as an interface that is like monads, but which allows for more static information about the constructed computations to be extracted. However, in contrast to monads, arrows do not directly allow intermediate values to be \emph{named}; instead, expressions must be written in \emph{point-free style}. 

As an example, an arrow computation which feeds the same input to two arrows, and adds their outputs, can be expressed in point-free style as follows:
\begin{code}
addA :: Arrow a => a x Int -> a x Int -> a x Int
addA f g =  arr (\x -> (x,x))  >>> first f >>> 
            second g           >>> arr (\(x,y) -> x + y)
\end{code}
With monads, a similar computation can be written more clearly by naming intermediate values:
\begin{code}
addM :: Monad m =>  (x -> m Int) -> (x -> m Int) -> 
                    (x -> m Int)
addM f g = \z ->
    do  x <- f z
        y <- g z
        return (x + y)
\end{code}
To overcome this downside of arrows, Paterson introduced arrow notation~\cite{arrownot}. In this notation, the above arrow computation can be written as follows:
\begin{code}
addA :: Arrow a => a b Int -> a b Int -> a b Int
addA f g = procb z -> do
   x <- f -< z
   y <- g -< z
   returnA -< x + y
\end{code}
Specialized compiler support is offered by \ghc{}, which desugars this notation into point free expressions. 

With the Key monad, we can name intermediate values in arrow
computations using \emph{regular} monadic do notation, without relying
on specialized compiler support. The |addA| computation above can be expressed using our \emph{embedded} arrow notation as follows: 
\begin{code}
addA :: Arrow a => a b Int -> a b Int -> a b Int
addA f g = proc $ \z -> do
    x <- f -< z
    y <- g -< z
    return $ (+) <$> x <*> y
\end{code}
We use a function conveniently called |proc| and use an infix function conveniently called |(-<)|.

The difference between |do| notation and arrow notation is that in arrow notation, one cannot observe intermediate values to decide what to do next. For example, we \emph{cannot} do the following:
\begin{code}
ifArrow ::  a Int x -> a Int x -> a Int x
ifArrow t f = procb z -> do
   case z of
     0 -> t -< z
     _ -> f -< z
\end{code}
Allowing this kind of behavior would make it impossible to translate arrow notation to arrow expressions, because this is exactly the power that monads have but that arrows lack \cite{idiomarrmonad}. To mimic this restriction in our embedded arrow notation, our function |(-<)| has the following type:
\begin{code}
(-<) :: Arrow a => a x y -> Cage s x -> 
              ArrowSyn s (Cage s y)
\end{code}
The type |ArrowSyn| is the monad which we use to define our embedded
arrow notation. The input and output of the arrow computations are
enclosed in |Cage|s, a type which disallows observation of the value of type |x| it ``contains''. 

\subsection{Implementing embedded arrow syntax}

\pablo{I don't really like |liberate| here. It is linguistically
  ill-typed because it is normally applied to
  people or countries/regions/cities, not individual objects. I propose |open|.}

The implementation of a |Cage| is as follows:
\begin{code}
newtype Cage s x = Cage { liberate :: KeyMap s -> x }
  deriving (Functor, Applicative)
\end{code}
Informally, a |Cage| ``contains'' a value of type |x|, but in reality
it does not contain a value of type |x| at all: it is a function from
a |KeyMap| to a value of type |x|. Hence we can be sure that
arrow computations returning a |Cage| do not allow pattern-matching on the result,
% we do not allow pattern matching on the result of an arrow
% computation
because the result is simply not available.

In our construction, we use |Key|s as names, and and |KeyMap|s as
\emph{enviroments}, i.e. mappings from names to values.  Each result
of an arrow via |(-<)| has its own name. A |Cage| stands for an
expression, i.e. a function from environment to value, which may
lookup names in the environment. As seen before, the Key monad in
conjunction with |KeyMap|s allows us to model \emph{heterogeneous} environments which can be extended \emph{without changing} the \emph{type} of the environment, which is exactly the extra power we need to define this translation. 

By using |(-<)| and the monad interface, we can construct the syntax for the arrow computation that we are expressing. Afterwards, we use the following function to convert the syntax to an arrow:
\begin{code}
proc ::  Arrow a => 
         (forall s. Cage s x -> ArrowSyn a s (Cage s y)) 
         -> a x y
\end{code}

Internally, the |ArrowSyn| monad builds an \emph{environment arrow}, an arrow from environment to environment, i.e. an arrow of type |a (KeyMap s) (KeyMap s)|. The |ArrowSyn| monad creates names for values in these environments using |KeyM|.
\begin{code}
newtype ArrowSyn a s x =
    AS (WriterT (EnvArrow a s) (KeyM s) x)
       deriving (Functor,Applicative,Monad)
type EnvArrow a s = EndoA a (KeyMap s)
\end{code}
The type |EndoA a x| is isomorphic to an arrow from a type |x| to the same type:
\begin{code}
newtype EndoA a x = EndoA (a x x)
\end{code}
Such arrows form a monoid as follows:
\begin{code}
instance Arrow a => Monoid (EndoA a x) where
    mempty = EndoA (arr id)
    mappend (EndoA l) (EndoA r) = EndoA (l >>> r)
\end{code}
The standard writer monad transformer, |WriterT|, produces |mempty| for |return|, and composes the built values from from the left and right hand side of |>>=| using |mappend|, giving us precisely what we need for building arrows. 





To define the operations |proc| and |(-<)|, we first define some auxiliary functions for manipulating environments. 
We can easily convert a name (|Key|) to the expression (|Cage|) which consists of looking up that name in the environment:
\begin{code}
toCage :: Key s a -> Cage s a
toCage k = Cage (\env -> lookup k env)
\end{code}
We can introduce an environment from a single value, when given a name (|Key|) for that value: 
\begin{code}
introEnv :: Arrow a => Key s x -> a x (KeyMap s)
introEnv k = arr (\v -> insert k v empty)
\end{code}
We also define an arrow to eliminate an environment, by interpreting an expression (|Cage|) using that environment:
\begin{code}
elimEnv :: Arrow a => Cage s x -> a (KeyMap s) x
elimEnv c = arr (liberate c)
\end{code}
Next to introducing and eliminating environments, we also need to extend an environment and evaluate an expression while keeping the environment:
\begin{code}
extendEnv :: Arrow a =>  Key s x ->
                         a (x, KeyMap s) (KeyMap s)
extendEnv k = arr (uncurry (insert k))

withEnv :: Arrow a =>  Cage s x ->
                       a (KeyMap s) (x, KeyMap s)
withEnv c = dup >>> first (elimEnv c)
    where dup = arr (\x -> (x,x))
\end{code}

With these auxiliary arrows, we can define functions that convert back and forth between a regular arrow and an environment arrow. To implement |(-<)|, we need to convert a regular arrow to an environment arrow, for which we need an expression for the input to the arrow, and a name for the output of the arrow:
\begin{code}
toEnvArrow ::  Arrow a =>  
           Cage s x  -> Key s y   -> 
           a x y -> EnvArrow a s
toEnvArrow inC outK a  = EndoA $ 
   withEnv inC >>> first a >>> extendEnv outK
\end{code}
We first produce the input to the argument arrow, by interpreting the input expression using the input environment. We then execute the argument arrow, and bind its output to the given name to obtain the output environment. 

The |-<| operation gets the arrow and the input expression as an argument, creates a name for the output, and then passes these three to |toEnvArrow|:
\begin{code}
(-<) :: Arrow a =>
        a x y ->
        (Cage s x -> ArrowSyn a s (Cage s y))
a -< inC = AS $
   do  outK <- lift newKey
       tell (toEnvArrow inC outK a)
       return (toCage outK)
\end{code}

In the other direction, to implement |proc| we need to convert an environment arrow to a regular arrow, for which we instead need the name of the input and an expression for the output:
\begin{code}
fromEnvArrow ::  Arrow a =>
             Key s x   -> Cage s y  ->
             EnvArrow a s -> a x y
fromEnvArrow inK outC (EndoA a)  =
   introEnv inK >>> a >>> elimEnv outC
\end{code}
We first bind the input to the given name to obtain the input environment. We then transform this environment to the output environment by running the arrow from environment to environment. Finally, we interpret the output expression in the output environment to obtain the output.

The |proc| operation creates a name for the input and passes it to the function as an expression to obtain the output expression and the environment arrow. We then convert the obtained arrow from environment to environment using |fromEnvArrow|:
\begin{code}
proc ::  Arrow a =>
             (forall s. Cage s x -> ArrowSyn a s (Cage s y)) ->
             a x y
proc f = runKeyM $
      do  inK <- newKey
          let AS m = f (toCage inK)
          (outC, a) <- runWriterT m
          return (fromEnvArrow inK outC a)
\end{code} 

\subsection{Discussion}

Altenkirch, Chapman and Uustalu\cite{relmonad} show a related construction: that in category theory arrows are a special case of \emph{relative monads}, which are themselves a generalization of monads. A relative monad is an instance of the following type class:
\begin{code}
class RelativeM m v where
  rreturn  :: v x -> m x
  (.>>=)   :: m x -> (v x -> m y) -> m y
\end{code}
The only difference with regular monads is that the values resulting from computations must be wrapped in a type constructor |v|, instead of being ``bare''. The relative monad laws are also the same as the regular (Haskell) monad laws.
The construction of Altenkirch et al. construction is not a relative monad in Haskell, only in category theory. In particular their definition uses the Yoneda embedding, which does not allow us freely use bound values, instead it requires us to manually lift values into scope, in the same fashion as directly using de Bruijn indices. 

Because all the operations in |ArrowSyn| (namely |(-<)|) return a |Cage|, it might be more informative to see it as a relative monad, i.e.:
\begin{code}
data ArrowRm a s x = ArrowRm 
         (ArrowSyn a s (Cage s x))
instance RelativeM (ArrowRm a s) (Cage s) where ...

(-<) :: a x y -> Cage s x -> ArrowRm a s y
proc :: (forall a. Cage s x -> ArrowRm a s y) -> a x y
\end{code}
In this formulation, it is clear that the user cannot decide what to do next based on the outcome of a computation: all we can get from a computation is |Cage|s. 
The monadic interface does not add extra power: while we cannot decide what to do next based on the output of a computation of type |ArrowSyn s (Cage s x)|, we can, for example, decide what to next based on the outcome of a computation of type |ArrowSyn s Int|. This does not give our embedded arrow notation more power than regular arrow notation or the relative monad interface: the value of the integer cannot depend on the result of an arrow computation and hence must be the result of a pure computation. This essentially the same trick as described in Svenningsson and Svensson\cite{bjorn}. 

As an aside, more generally, this trick can be used to give a monadic interface for \emph{any} relative monad:
\begin{code}
data RmM rm v a where
   Pure :: a -> RmM rm v a
   Unpure ::  rm a -> (v a -> RmM rm v b) 
              -> RmM rm v b

instance Monad (RmM rm v) where
  return = Pure
  (Pure x) >>= f = f x
  (Unpure m f) >>= g = Unpure m (\x -> f x >>= g)

fromRm :: RelativeM rm v => rm a -> RmM rm v (v a)
fromRm m = Unpure m (return)

toRm :: RelativeM rm v => RmM rm v (v a) -> rm a
toRm (Pure x)      = rreturn x
toRm (Unpure m f)  = m .>>= (toRm :. f)
\end{code}
The insight is because a computation monad must eventually return a value of |v a| to convert a relative monad computation via |toRm|, any pure value that is used, can eventually be removed via the monad law |return x >>= f == f x|. Our embedded arrow construction can be seen as relative monad, where we apply this trick to obtain a monadic interface.

Our construction hence suggests that arrows are also a special case of relative monad in Haskell with the key monad, but a formal proof (using the Key monad laws from Figure (\ref{laws}) is outside the scope of this paper. In the code online, we also show that this construction can be extended to use \emph{relative monadfix} (with function  |rmfix :: (v a -> m a) -> m a|) to construction arrows using |ArrowLoop|, but the we cannot use recursive monad notation in this case, because the above trick does not extend to Monadfix.


The \emph{Arrow Calculus}\cite{arrowcalc} describes a translation of a form of arrow syntax (not embedded in Haskell) to arrows which is very similar to the construction presented here. Their calculus has five laws, three of which can be considered to be relative monad laws, which they use to prove the equational correspondence between their calculus and regular arrows. Due to the similarity, their paper should provide a good starting point for anyone trying to prove the same for this construction.

\section{Representations of variables in Syntax}
\label{syntax}
What else can we do with the Key monad? The Key monad allows us to associate types with ``names'' (|Key|s), and to see that if two names are the same, then their associated types are also the same. Use cases for this especially pop up when dealing with representations of syntax with binders, as we will show next.

\subsection{Typed names}

A straightforward way to represent the syntax of a programming language is to simply use strings or integers as names. For example, the untyped lambda calculus can be represented as follows:
\begin{code}
type Name  =  Int
data Exp   =  Var Name
           |  Lam Name Exp
           |  App Exp Exp
\end{code}
If we want to represent a \emph{typed} representation of the lambda calculus, then this approach does not work anymore. Consider the following \gadt{}:
\begin{code}
data TExp a where
  Var  :: Name -> TExp a
  Lam  :: Name -> TExp b -> TExp (a -> b)
  App  :: TExp (a -> b) -> TExp a -> TExp b
\end{code}
We cannot do much with this datatype. If we, for example, want to write an interpreter, then there is no way to represent the environment: we need to map names to values of different types, but there is no type-safe way to do so.

With the Key monad, we \emph{can} extend this simple naming approach to typed representations, without adding |Typeable| constraints. Consider the following data type:
\begin{code}
data KExp s a where
  KVar  ::  Key s a -> KExp s a
  KLam  ::  Key s a -> KExp s b -> KExp s (a -> b)
  KApp  ::  KExp s (a -> b) -> KExp s a -> KExp s b
\end{code}
Because the names are now represented as keys, we can represented an environment as a |KeyMap|. We can even offer a Higher Order Abstract Syntax (\hoas{}) \cite{hoas} interface for constructing such terms by threading the key monad computation, which guarantees that all terms constructed with this interface are well-scoped:
\begin{code}
class Hoas f where 
  lam :: (f a -> f b)  -> f (a -> b)
  app :: f (a -> b)    -> (f a -> f b)

newtype HoasKey s a = 
  HK { getExp :: KeyM s (KExp s a) }

instance Hoas (HoasKey s) where
  lam f = HK $ 
     do  k <- newKey 
         b <- getExp $ f $ HK $ pure $ KVar k
         return (KLam k b)
  app f x  = HK $ KApp <$> getExp f <*> getExp x 
\end{code}
For instance, the lambda term |(\x y -> x)| can now be constructed with: |lam (\x -> lam (\y -> x))|

\subsection{Translating well-scoped representations}

The datatype |KExp| does not ensure that any value of type |KExp| is well-scoped. As far as we know, there two are approaches to constructing data types for syntax which ensure that every value is well-scoped.  The first is parametric Higher Order Abstract Syntax (\hoas{})\cite{phoas, ags, graphs}, and the second is using typed de Bruijn indices\cite{nested}. However, there seems to be no way type-safe way to translate terms created with a parametric \hoas{} term to typed de Bruijn indices, but the Key monad allows us to cross this chasm.
 
In parametric \hoas{}, typed lambda terms are represented by the following data type:
\begin{code}
data Phoas v a where
  PVar  :: v a -> Phoas v a
  PLam  :: (v a -> Phoas v b) -> Phoas v (a -> b)
  PApp  :: Phoas v (a -> b) -> Phoas v a -> Phoas v b
\end{code}
The reading of the type parameter |v| is the type of \emph{variables}.
For example, the lambda term |(\x y -> x)| can be constructed as follows:
\begin{code}
phoasExample :: Phoas v (x -> y -> x)
phoasExample = PLam (\x -> PLam (\y -> x))
\end{code}
An attractive property of parametric \hoas{} is that we use Haskell binding to construct syntax, and that terms of type |(forall v. Phoas v a)| are always well-scoped\cite{phoas}.

The second way to ensure well-scopedness is to use typed de Bruijn indices. We present our own modern variant of this technique using Data Kinds and \gadt s, but the idea is essentially the same as presented by Bird and Paterson \cite{nested}. Our representation of typed de Bruijn indices is an index in a heterogeneous list (Figure \ref{heteros}). A typed de Bruijn index of type |Index l a| is an index for a variable of type |a| in an environment where the types of the variables are represented by the type level list |l|. We can use these indices to represent lambda terms as follows:
\begin{code}
data Bruijn l a where
  BVar  :: Index l a -> Bruijn l a
  BLam  :: Bruijn (a : l) b -> Bruijn l (a -> b)
  BApp  :: Bruijn l (a -> b) -> Bruijn l a -> Bruijn l b
\end{code}
A closed term of type |a| has type |Bruijn [] a|.

\begin{figure}
\begin{code}
data Index l a where
  Head  :: Index (h : t) h
  Tail  :: Index t x -> Index (h : t) x

data TList l f where
  TNil  :: TList [] f
  (:::) :: f h -> TList t f -> TList (h : t) f

index :: TList l f -> Index l a -> f a
index (h ::: _) Head     = h
index (_ ::: t) (Tail i) = index t i

instance PFunctor (TList l) where
  pfmap f TNil      = TNil
  pfmap f (h ::: t) = f h ::: pfmap f t
\end{code}
\caption{Heterogeneous list and indexes in them.}
\label{heteros}
\end{figure}

The types |(forall v. Phoas v a)| and |(Bruijn [] a)| both represent well-scoped typed lambda terms (and |undefined|), and translating from the latter to the former is straightforward. However, there seems to be no way to translate the former to the latter, without using extensions such as the Key monad. In other words there seems to be no function of type:
\begin{code}
phoasToBruijn :: (forall v. Phoas v a) -> Bruijn [] a
\end{code} 
This seems to be not only be impossible in Haskell without extensions, but in dependently typed languages without extensions as well. When using |Phoas| in \emph{Coq} to prove properties about programming languages, an small extension to the logic in the form of a special well-scopedness axiom for the |Phoas| data type is needed to translate Phoas to de Bruijn indices\cite{phoas}.

The well-scopedness of variables in a |Bruijn| value follows from the fact that the value is well-typed. With |Phoas|, the well-scopedness relies on the meta-level (i.e. not formalized through types) argument that no well-scoped values can be created by using the |Phoas| interface. The internal (i.e. formalized through types) well-scopedness of |Bruijn|, allows interpretations of syntax which seem to not be possible if we are using terms constructed with |Phoas|. As an example of this, consider translating lambda terms to \emph{Cartesian closed category} combinators (the categorical version of the lambda calculus). This can be done if the lambda terms are given as |Bruijn| values, as demonstrated in Figure \ref{ccc}. Without the Key monad, there seem to be no way to do the same for terms constructed with the Phoas terms.

Our implementation of |phoasToBruijn| works by first translating |Phoas| to the |KExp| from the previous subsection, and then translating that to typed de bruijn indices. The first step in this translation is straightforwardly defined using the |Hoas| interface from the previous subsection: 
\begin{code}
phoasToKey :: (forall v. Phoas v a) -> (forall s. KeyM s (KExp s a))
phoasToKey v = getExp (go v) where
  go :: Phoas (HoasKey s) a -> HoasKey s a
  go (PVar v)    = v
  go (PLam f)    = lam (go . f)
  go (PApp f x)  = app (go f) (go x)
\end{code}

We will now show how we can create a function of type:
\begin{code}
keyToBruijn :: KExp s a -> Bruijn [] a
\end{code}
Using this function, we can then implement |phoasToBruijn| as follows:
\begin{code}
phoasToBruijn :: (forall v. Phoas v x) -> Bruijn [] x
phoasToBruijn p = 
  runKeyM (keyToBruijn <$> phoasToKey p)
\end{code}
To implement the |keyToBruijn| function, we need a variant of the |Box| we saw previously:
\begin{code}
data FBox s f where
  FLock :: Key s a -> f a -> FBox s f

funlock :: Key s a -> FBox s f -> Maybe (f a)
funlock k (FLock k' x) =
  case testEquality k k' of
    Just Refl  -> Just x
    Nothing    -> Nothing
\end{code}
The difference with |Box| is that we now store values of type |f a| instead of values of type |a| in the box. We provide a variant of |fmap| for this container:
\begin{code}
class PFunctor p where
  pfmap :: (forall x. f x -> g x) -> p f -> p g

instance PFunctor (FBox s) where
  pfmap f (FLock k x) = FLock k (f x)
\end{code} We also need a variant of the |KeyMap|, where we store |FBox|es instead of regular boxes:
\begin{code}
newtype FKeyMap s f = FKm [FBox s f]
insert :: Key s a -> f a -> FKeyMap s f  -> FKeyMap s f
lookup :: Key s a -> FKeyMap s f -> Maybe (f a)
instance PFunctor (FKeyMap s)
\end{code}

We store the current ``environment'' as a |FKeyMap| mapping each |Key| to an |Index| in the current environment. When we enter a lambda-body, we need to extend the environment with a new name mapping to the de Bruijn index |Head|, and add one lookup step to each other de Bruijn index currently in the |FKeyMap|. This is be done as follows:
\begin{code}
extend :: Key s h -> FKeyMap s (Index t) ->
            FKeyMap s (Index (h : t))
extend k m = insert k Head (pfmap Tail m)
\end{code}
With this machinery in place, we can translate |KExp| to |Bruijn| as follows:
\begin{code}
keyToBruijn :: KExp s a -> Bruijn [] a
keyToBruijn = go empty where
  go :: FKeyMap s (Index l) -> KExp s x -> Bruijn l x
  go e (KVar v)    = BVar (e ! v)
  go e (KLam k b)  = BLam (go (extend k e) b)
  go e (KApp f x)  = BApp (go e f) (go e x)
\end{code}
Note that |keyToBruijn| fails if the input |KExp| is ill-scoped. This cannot happen when |keyToBruijn| is called from |phoasToBruijn| because |phoasToKey| will always give well-scoped values of type |KExp|. This relies on the meta-level argument that values of type |PHoas| are always well-scoped. We stress that hence the key monad extension \emph{cannot} serve as a replacement of well-scopedness axiom used in a dependently typed setting. 


\begin{figure}
\begin{code}
class Category c => CCC c where
    prod     :: c x a -> c x b -> c x (a,b)
    fst      :: c (a,b) a
    snd      :: c (a,b) b
    curry    :: c (a,b) x -> c a (b -> x)
    uncurry  :: c a (b -> x) -> c (a,b) x

toClosed :: CCC c =>  Bruijn [] (x -> y) -> 
                      c () (x -> y)
toClosed p = go p TNil where
  go :: CCC c => Bruijn l y -> TList l (c x) -> c x y
  go (BVar x)    e = index e x
  go (BLam b)    e = 
    curry $ go b (snd ::: HK (. fst) e)
  go (BApp f x)  e = uncurry (go f e) . prod id (go x e)

instance PFunctor (TList l) where
  pfmap f TNil      = TNil
  pfmap f (h ::: t) = f h ::: pfmap f t
\end{code}
\label{ccc}
\caption{Translating lambda terms to Cartesian closed categories.}
%$
\end{figure}


\section{Safety of the Key monad}
\label{safety}

In this section, we precisely state what we mean by safety, and informally argue for the safety of the Key monad.

\subsection{Type safety}

The first safety property that we conjecture the Key monad has is \emph{type safety}: |testEquality| will never allow us to prove that |a :~: b| if |a| and |b| are \emph{distinct} types. Informally, the justification for this is that a key value |k| of type |Key s a| together with the type |s|, which we call the \emph{scope type variable},  \emph{uniquely determine} the associated type |a| of the key. Hence, when two key values and scope type variables are the same\footnote{Even though users cannot compare keys explicitly, implementations of the Key monad internally represent keys by some underlying value that can be compared for equality.}, their associated types \emph{must be the same} as well. 

The argument why the scope type variable |s| and the key value |k| together uniquely determine type |a| goes as follows:
\begin{enumerate}
\item Each execution of a Key monad computation has a scope type variable |s| that is distinct from the scope type variables of all other Key monad computations. This is ensured by the type of |runKeyM|, namely |(forall s. KeyM s a) -> a|, which states that the type |s| cannot be unified with any other type. 
\item Each |newKey| operation in such a Key monad computation gives a value that is unique within the scope determined by |s|, i.e. distinct from other keys created in the same computation.
\item Each key only has \emph{a single type} associated with it. This is ensured by the type of |newKey|, which only allows us to construct a key with a single type, i.e. not a key of type |forall a. Key s a|, because the type of a hypothetical function |createPolymorphicKey :: KeyM (forall a. Key s a)| would not unify with the type of |newKey|. 
\end{enumerate}




\subsection{Referential transparency} 

The second safety property that we are concerned with is \emph{referential transparency}. More precisely, in an otherwise pure language with the Key monad extension, does the following still hold?
\begin{code}
let x = e in (x,x) ==  (e,e) 
\end{code}

In other words, referential transparency means that an expression always evaluates to the same result in any context. Our implementation of the key monad only relies on \emph{unsafeCoerce}; it does not use \emph{unsafePerformIO}, nor does it use |unsafeCoerce| to convert an |IO a| action to a pure value and hence referential transparency cannot be broken by this implementation. Since the |ST| monad can be implemented using the Key monad, the same can be said for the \st{} monad. 
However, more efficient implementations of the \st{} monad uses \emph{global} pointers respectively, which does rely on features that might potentially break referential transparency.


\subsection{Abstraction safety} 
Abstraction safety is the property that we cannot break the abstraction barriers which are introduced through existential types. For example, consider the following existential type:
\begin{code}
data AbsBool where
  AbsBool ::  Eq a => a -> a -> (a -> b -> b -> b) 
              -> AbsBool
\end{code}
Let us consider two different uses of this type:
\begin{code}
boolBool = 
  AbsBool True False (\c t f -> if c then t else f) 
boolInt  = 
  AbsBool  0 1        (\c t f -> if c == 0 then t else f)
\end{code}
If our language is abstraction safe, then it is impossible to observe any difference between |boolBool| and |boolInt|. This property is formalized by \emph{parametricity} (which also gives ``free'' theorems\cite{theoremsforfree}). A typical example of a primitive which is not abstraction safe (but is type-safe) is a primitive that allows us to check the equality of any two types:
\begin{code}
badTest :: a -> b -> Maybe (a :~: b)
\end{code}

The primitive |testEquality| is similar to the |badTest| primitive above, and indeed our operations on |Box| do allow us to ``break the abstraction barrier'': if |unlock| succeeds, we have learned which type is hidden in the |Box|. However, finding out which type is hidden by an existential type can not only be done with the Key monad, but also by the established Generalized Algebraic Data types extension of Haskell. For example, suppose we have the following type:
\begin{code}
data IsType a where
  IsBool  :: IsType Bool
  IsInt   :: IsType Int
  IsChar  :: IsType Char
\end{code}
We can then straightforwardly implement a variant of |testEquality|:
\begin{code}
testEquality :: IsType a -> IsType b -> Maybe (a :~: b)
testEquality IsBool  IsBool  = Just Refl
testEquality IsInt   IsInt   = Just Refl
testEquality IsChar  IsChar  = Just Refl
testEquality _       _       = Nothing
\end{code}

There are, however, formulations of parametricity which state more precisely exactly which abstraction barrier cannot be crossed \cite{type-safecast, bernardy_proofs_2012}. In these formulations, |boolBool| and |boolInt| are indistinguishable. We can think of |runKeyM| as an operation which dreams up a specific Key \gadt{} for the given computation, for example:
\begin{code}
data Key A a where
  Key0 :: Key A Int
  Key1 :: Key A Bool
  ...
\end{code}
Here |A| is a globally unique type associated with the computation. This interpretation is a little tricky: since a Key computation might create an infinite number of keys, this hypothetical datatype might have an infinite number of constructors. Alternatively, we can interpret keys as \gadt s that index into a type-level list or type-level tree, as we do in Section \ref{impl}.  We conjecture that there is a variant of parametricity for Haskell extended with the Key monad in which, in analogy with parametricity for \gadt s, |boolBool| and |boolInt| above are considered to be indistinguishable. 


\subsection{Normalization}

A fourth desirable property of a type system extension is preservation of normalization, i.e.,
the property that ensures well-typed terms always have a normal form. 
%What this usually means is that type-safe programs that do not use recursion terminate.
Although standard typed $\lambda$-calculi (such as System F) are normalizing, Haskell is not, as we can write non-terminating programs. Even without term-level recursion, we can create programs that do not terminate by using type-level recursion. However, if we disallow contravariant recursion at the type level (i.e.\ type-level recursive occurrences that occur to the left of a function arrow), then all Haskell programs without term-level recursion (and use of |undefined|) do terminate.

It turns out that extending a normalizing language with the Key monad breaks normalization.
%, even when we disallow covariant recursion on the type level and recursion at the term level. 
We show this by implementing a general fixpoint combinator |fix| which uses neither contravariant recursion at the type level nor term-level recursion.

\begin{figure}
\begin{code}
data D s a 
   =  Fun (Box s -> D s a)
   |  Val a

lam :: Key s (D s a) -> (D s a -> D s a) -> D s a
lam k f = Fun (f . fromJust . unlock k)

app :: Key s (D s a) -> D s a -> D s a -> D s a
app k (Fun f) x = f (Lock k x)

fix :: (a -> a) -> a
fix f = runKeyM $
   do  k <- newKey
       let f'    = lam k (Val . f . unVal)
           xfxx  = lam k (\x -> app k f' (app k x x))
           fixf  = app k xfxx xfxx
       return (unVal fixf)
 where unVal (Val x) = x
\end{code}
\label{fig:fix}
\caption{Implementing a general fixpoint combinator without term-level recursion nor type-level contravariant recursion}
\end{figure}
%$
Fig.\ \ref{fig:fix} presents the implementation of |fix|. First, we introduce a datatype |D s a| for domains representing models of the untyped lambda calculus. (We are going to encode the standard fixpoint combinator |\f -> (\x -> f (x x)) (\x -> f (x x))| in this domain.) An element of |D s a| is either a function over |D s a| or a value of type |a|. Normally, we would use contravariant recursion for the argument of |Fun|, but we are not allowed to, so we mask it by using a |Box s| instead. As a result, |D s a| is not contravariantly recursive, and neither are any of its instances.

Second, we introduce two helper functions: |lam|, which takes a function over the domain, and injects it as an element into the domain, and |app|, which takes two elements of the domain and applies the first argument to the second argument. Both need an extra argument of type |Key s (D s a)| to lock/unlock the forbidden recursive argument.

Third, the fixpoint combinator takes a Haskell function |f|, wraps it onto the domain |D s a| resulting in a function |f'|, and then uses |lam| and |app| to construct a fixpoint combinator from the untyped lambda calculus. Lastly, we need to convert the result from the domain |D s a| back into Haskell-land using |unVal|.

What this shows is that (1) adding the Key monad to a normalizing language may make it non-normalizing, (2) the Key monad is a genuine extension of Haskell without term-level recursion and type-level contravariant recursion. Incidentally, this is also the case for the \st{} monad. In a stratified type system with universe levels, such as Agda or Coq, it should be possible to omit this problem by making keys of a higher level than their associated types.

\section{Implementing the Key monad}
\label{impl}
Is the Key monad expressible in Haskell directly, without using |unsafeCoerce|? Can we employ more recent advancements such as  \gadt s to ``prove'' to the type system that the Key monad is safe? In this section, we argue and motivate that the answer to this question is most likely ``no'' by exploring how far we can get. 

\subsection{Implementation using |unsafeCoerce|}

To get a feel for possible implementations of the Key monad, let us first consider a straightforward implementation, using \emph{unsafeCoerce}, in which we give each key a unique name. One could implement generating unique names using a state monad, but the |(purity)| key monad law (|m >> n == n)| would then not hold. Instead, we implement the Key monad using an splittable name supply, with the following interface:
\begin{code}
newNameSupply  :: NameSupply
split          ::  NameSupply -> 
                   (NameSupply , NameSupply)
supplyName     :: NameSupply -> Name
\end{code}

One implementation of the |NameSupply| uses paths in a binary tree:
\begin{code}
data TreePath = Start | Left TreePath | Right TreePath
\end{code}
When reading left-to-right, these paths are given in reverse order from the root: the path |Left (Right Start)| is a path to the left child of the right child of the root. A name is then a path to leaf in a tree, and a name supply is a path to a subtree. To split a |NameSupply|, we convert a path to a node into a path to the two children of that node:
\begin{code}
type NameSupply  = TreePath
type Name        = TreePath
newNameSupply  = Start
split s        = (Left s, Right s)
supplyName     = id
\end{code}

Using such name supplies, the implementation of the Key monad is as follows:
\begin{code}
data KeyM s a = 
  KeyM { getKeyM :: NameSupply -> a }
data Key s a   = Key Name

newKey :: KeyM s (Key s a)
newKey = KeyM $ \s -> Key (supplyName s)

instance Monad (KeyM s) where
  return x      = KeyM $ \_ -> x
  m >>= f       = KeyM $ \s ->
     let (sl,sr) = split s
     in getKeyM (f (getKeyM m sl)) sr

runKeyM :: (forall s. KeyM s a) -> a
runKeyM (KeyM f)  = f newNameSupply

testEquality (Key l) (Key r) 
  | l == r     = Just (unsafeCoerce Refl)
  | otherwise  = Nothing
\end{code}

A |KeyM| computation consisting of |>>=|,|return| and |newKey| can also be seen as a binary tree where binds are node, |newKey|s are leaves and |return|s are empty subtrees. The |Name| associated with each key is the path to the |newKey| that created it, in the tree that corresponds to the |KeyM| computation. For example, the Key resulting from the |newKey| in the expression:
\begin{code}
runKeyM $ (m >> newKey) >>= f
\end{code}
will get the name |Right (Left Start)|.

\subsection{The key indexed monad}

Can we formalize through types the invariant that when two keys are the same their types must also be the same? It turns out we can, but this adds more types to the interface, leading to a loss of power of the construction.

The crucial insight is that is needed for this implementation, is that it \emph{is} possible to implement to compare two indices in a heterogeneous list (Fig \ref{heteros}), and if they are equal, then produce a that the proof types are equal, as follows:
\begin{code}
testEquality :: Index l a -> Index l b -> Maybe (a :~: b)
testEquality Head      Head      = Just Refl
testEquality (Tail l)  (Tail r)  = testEquality l r
testEquality _         _         = Nothing
\end{code}

We can employ the same insight to construct |testEquality| function for other data types. Instead of indexes in a heterogeneous list, we add types to the paths in a tree to obtain  \emph{paths in a hetrogenous tree}. For this datatype we need to be able to construct type-level trees, for which we use the following data type as a data-kind:
\begin{code}
data Tree a = Empty | Single a | Tree a :++: Tree a
\end{code}
With this datatype, we can construct types of kind |Tree| |*| such as:
\begin{code}
Single Int :++: (Single Bool :++: Single String)
\end{code}
We can now adapt the datatype |TreePath| to provide paths in type-level trees instead of value-level trees, in a similar fashion to how |Index| is an index in a type-level list instead of a value-level list:
\begin{code}
data TTreePath p w where
  Start   :: TTreePath w w
  Left    :: TTreePath (l :++: r) w -> TTreePath l w
  Right   :: TTreePath (l :++: r) w -> TTreePath r w
\end{code}

We can now construct a |testEquality|-like function of the following type:
\begin{code}
samePath ::  TTreePath p w -> TTreePath p' w 
             -> Maybe (p :~: p')
\end{code}
The implementation of this function is a bit more involved than for |Index|, but is unsurprising:
\begin{code}
samePath Start      Start      = Just Refl
samePath (Left l)   (Left r)   = weakL  <$> samePath l r
samePath (Right l)  (Right r)  = weakR  <$> samePath l r
samePath _          _          = Nothing where 
  weakL :: ((l :++: r) :~: (l' :++: r')) -> l :~: l'
  weakL x = case x of Refl -> Refl

  weakR :: ((l :++: r) :~: (l' :++: r')) -> r :~: r'
  weakR x = case x of Refl -> Refl
\end{code}
We can use this function to implement a function that produces a proof that if two paths to a leaf are the same, then their associated types are the same:
\begin{code}
sameLeaf ::  TTreePath (Leaf p) w ->
             TTreePath (Leaf p') w -> 
             Maybe (p :~: p')
sameLeaf l r = weakenLeaf <$> samePath l r where
  weakenLeaf :: (Leaf p :~: Leaf p') -> p :~: p'
  weakenLeaf x = case x of Refl -> Refl
\end{code}

Now that we have encoded the invariant that when two key values are the same then their associated types must also the same, we can use this to implement a \emph{typed} name supply with the following interface:
\begin{code}
type TNameSupply l s = TTreePath l s
type TName s a = TTreePath (Single a) s

newTNameSupply :: TNameSupply s s
tsplit ::  TNameSupply (l :++: r) s 
           -> (TNameSupply l s, TNameSupply r s)
supplyTName :: TNameSupply (Leaf a) s -> TName s a
sameName ::  TName s a -> TName s b -> 
             Maybe (a :~: b)
\end{code}
A typed name supply of type |TNameSupply l s| gives unique names for the types in the subtree |l| which can be tested for equality, using |sameName|, with all names which are created in the context |s|. The implementations of the name supply functions are completely analogous to their untyped counterparts.

By using the typed name supply instead of the regular name supply and altering the types in the interface to reflect this change, we obtain an implementation of what we call the \emph{indexed} the Key monad, with the following interface:
\begin{code}
newKeyIm        ::  KeyIm s (Single a) (Key s a)

rreturn        ::  a -> KeyIm Empty s a
(.>>=)        ::  KeyIm s l a -> (a -> KeyIm s r b) 
                  -> KeyIm s (l :++: r) b

runKeyIm      :: (forall s. KeyIm s l a) -> a

testEquality  ::  Key s a -> Key s b -> Maybe (a :~: b)
\end{code}
The implementation of this interface is completely analogous to the implementation of the key monad in the previous subsection. The only difference is that |testEquality| now uses |sameName|, omitting the need for |unsafeCoerce|.
This interface is an instance of the \emph{parametric effect monad} type class\cite{peff}. 

Note that in the implementation |runKeyIm| now uses the universally quantified type variable to |s| to unifiy |s| with |l|, to use |newTNameSupply|. This ``closes the context'', stating that the context is precisely the types which are created in the computation. In contrast, in |runKeyM| the type variable was not given an interpretation.

While we have succeeded in avoiding |unsafeCoerce|, this construction is \emph{less powerful} than the regular key monad because the types of the keys which are going to be created must now be \emph{statically known}. All example use cases of the key monad in this paper rely on the fact that the type of the keys which are going to be created do not have to be statically know. For example, we cannot implement a translation from parametric \hoas{} to de Bruijn indices with |KeyIm|, because the type of the keys which will have to be created is precisely the information that a parametric \hoas{} representation lacks.

\subsection{Attempting to recover the Key monad}

Can we formalize the invariant through types and provide the regular Key monad interface? An obvious attempt at this is hiding the extra type of |KeyIm|:
\begin{code}
data KeyM s a where
  KeyM :: KeyIm s p a -> KeyM s a
\end{code}
We denote this type by |exists p. KeyIm s p a| for presentational purposes, which is not valid (\ghc{}) Haskell. While this allows us to provide type-safe implementations of |testEquality|, |fmap|, |newKey| and |return|, things go awry for |join| (or |>>=|) and |runKeyM|.

The first problem arises at |runKeyM|. We get the type:
\begin{code}
runKeyM :: (forall s. exists p. KeyIm s p a) -> a
\end{code}
But to use |runKeyIm| the type should be:
\begin{code}
runKeyM :: (exists p. forall s. KeyIm s p a) -> a
\end{code}
These types are \emph{not} equivalent: the latter implies the former, but not the other way around. In the former, the type which is bound to |p| may depend on |s|, which cannot happen in the latter. 

 If the types of all keys which are created do not mention |s|, we do not for example create a key of type |Key s (Key s a)|, then one could argue that coercing the computation from the former to the latter is perfectly safe. However, if we create a key of type |Key s (Key s Int)|, then when the type |s| is unified with the tree of types of the keys, this leads to a \emph{cyclic} types. For example:
\begin{code}
s ~ (Key s Int) :++: t
\end{code} 
In the previous section, we demonstrated that allowing such keys, where the type of the key mentions |s|, allows us to write |fix| without recursion. Apart from that, it seems that these particular cyclic types does not do any harm (we already had nontermination in Haskell), and it is likely to be safe to coerce the first type of |runKeyM| to the latter. However, it is highly unlikely that we can formalize this through types that this coercion is safe: the Haskell type system does not allow cyclic types. Even if it did, it is unclear to us how to prove that this coercion is safe.

For |join| other problems arise. We need a implementation of type:
\begin{code}
join ::  (exists p. KeyIm s p (exists q. KeyIm s q a)) -> 
         exists r. KeyIm s r a
\end{code}
Expanding the definition of |KeyIm|, the type of the \emph{argument} we have is:
\begin{code}
exists p. TNameSupply p s -> exists q. TNameSupply q s -> a
\end{code} 
However, to use the implementation of |join| of |KeyIm|, we need the argument to be of type:
\begin{code}
exists p q. TNameSupply p s ->  TNameSupply q s -> a
\end{code}
Again, these two types are \emph{not} equivalent: the latter implies the former, but not the other way around. In this situation we know more about the possible argument values than the types suggest. We know that Key is an abstract type for the user, who only has access to |testEquality|, not the constructors of Key. Hence the \emph{user-supplied} argument function cannot distinguish between different values of the type |TNameSupply p s|. For example, the values |Left Start| and |Left (Left Start)| are indistinguishable for the argument function: they are only used to create unique names, and test them for equality, not to observe their exact value. 

For this reason, the type that is bound to |q| is \emph{the same type} for all values of |TNameSupply p s|. Hence, it should be safe to coerce the argument from the former type to the later type. However, formalizing this through types seems unlikely. One could try formalizing the abstractness of the name supply by making the implementation polymorphic in the implementation of the name supply and names. One would then also need to formalize the exact behavior of the name supply, for example that the name supply acts in exactly the same way as the implementation with paths in trees. This property, cannot be encoded in the Haskell type system (yet), since it requires the types to constraint the exact behavior of functions in the implementation, which requires dependent typing.  Moreover, as far as we know it is already impossible to prove the following simpler property (which holds by parametricity) in Haskell: |(forall f. f x -> exists q. g q) -> (forall f. exists q. f x -> g q)|. Finally, when a computation creates an infinite number of keys, this will also lead to an \emph{infinite} type, which is not allowed in the Haskell type system. For these reasons, we feel that it is highly unlikely that the Key monad can be expressed in pure Haskell.


\section{Discussion on the \st{} monad proof}
\label{stdis}

The \st{} monad was introduced in \cite{stmonad} and contained some safety statements and also a high-level description of a proof. The proof sketch mentions the use of parametricity, which is a doubtful proof technique to use because it is not established that parametricity still holds for a language with the \st{} monad. A follow-up paper \cite{LaunchburySabry} mentions another problem with the first paper, in particular that implementations of the lazy \st{} monad may actually generate the wrong result in a setting that is more eager. This paper claims to fix those issues with a new semantics and proof sketch. However, a bug in this safety proof was discovered, which lead to a series of papers\cite{LaunchburySabry,AriolaSabry} formalizing the treatment of different versions of encapsulating strict and lazy state threads in a functional language, culminating in \cite{MoggiSabry}. This paper gives different formulations of strict and lazy state threads, one of them corresponding to lazy state threads in Haskell. The aim of the paper is to establish {\em type safety} of state threads. However, the paper only provides a proof sketch of type safety for one of the formulations, and only claims type safety (without a proof) for the other ones. With the exception of the original paper\cite{stmonad}, all these papers consider only \emph{local state}, that is, each state thread has its own memory, in contrast to the actual implementation of the \st{} monad.

Even if type safety may now be considered to have been established by these papers, we are still left with referential transparency and abstraction safety. We are unaware of any work that attempts to establish parametricity or referential transparency in the presence of the \st{} monad. Referential transparency is quite tricky for actual implementations of the \st{} monad since efficient implementations use global pointers. Abstraction safety is also very important because most people assume that parametricity in Haskell actually holds, without giving it a second thought that the \st{} monad may destroy it. 

Now, we actually believe that the \st{} monad (and also the Key monad) is safe in all of these senses. But we have also realized that there exist no actual proofs of these statements in the literature. We think that the Key monad, which is arguably simpler than the \st{} monad, could be a first step on the way to proving the \st{} monad safe.

\section{Conclusion}

In the \st{} monad, one of the invariants that must hold is that when two references are the same, then their types must also be the same. We presented the Key monad, which splits reasoning based on this invariant into a separate interface, and makes it available to user. We showed that this new interface gives a form of dynamic typing without the need for |Typeable| constraints, which allows us to do things we could not do before: implement the \st{} monad, implement an embedded form of arrow syntax and translate parametric \hoas{} to typed de Bruijn indices. The Key monad is simpler than the \st{} monad, since it embodies just one aspect of it. A full proof of the safety of the \st{} monad remains elusive to this day, and a proof of the safety of the Key might be a stepping stone towards it.

\label{conc}
\bibliographystyle{apalike}
\bibliography{refs}

\end{document}
