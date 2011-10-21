\begin{flushleft}\ttfamily\upshape
%BEGIN LATEX
\parindent 0pt
%END LATEX
\verb|#|pragma~JessieIntegerModel(math)~\\
\verb|#|pragma~JessieTerminationPolicy(user)~\\
~\\
\begin{slshape}/*@~\textbf{lemma}~mean~:~~\\
~~@~~~\textbf{\char'134 forall}~integer~x,~y;~x~<=~y~==>~x~<=~(x+y)/2~<=~y;~~\\
~~@*/\end{slshape}~\\
~\\
\begin{slshape}//@~\textbf{requires}~n~>=~0~\&{}\&{}~\textbf{\char'134 valid\_{}range}(t,0,n$-$1);\end{slshape}~\\
int~binary\_{}search(long~t[],~int~n,~long~v)~\{~\\
~~int~l~=~0,~u~=~n$-$1;~\\
~~\begin{slshape}//@~\textbf{loop}~\textbf{invariant}~0~<=~l~\&{}\&{}~u~<=~n$-$1;\end{slshape}~\\
~~\textbf{while}~(l~<=~u)~\{~\\
~~~~int~m~=~(l~+~u)~/~2;~\\
~~~~\textbf{if}~(t[m]~<~v)~\\
~~~~~~l~=~m~+~1;~\\
~~~~\textbf{else}~\textbf{if}~(t[m]~>~v)~\\
~~~~~~u~=~m~$-$~1;~\\
~~~~\textbf{else}~\textbf{return}~m;~~\\
~~\}~\\
~~\textbf{return}~$-$1;~\\
\}~\\
\end{flushleft}