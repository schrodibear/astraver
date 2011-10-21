\begin{flushleft}\ttfamily\upshape
%BEGIN LATEX
\parindent 0pt
%END LATEX
\begin{slshape}/*@~\textbf{lemma}~mean~:~\textbf{\char'134 forall}~integer~x,~y;~x~<=~y~==>~x~<=~(x+y)/2~<=~y;~*/\end{slshape}~\\
~\\
\begin{slshape}/*@~\textbf{requires}~n~>=~0~\&{}\&{}~\textbf{\char'134 valid\_{}range}(t,0,n$-$1);~\\
~~@~\textbf{ensures}~$-$1~<=~\textbf{\char'134 result}~<=~n$-$1;~\\
~~@*/\end{slshape}~\\
int~binary\_{}search(int*~t,~int~n,~int~v)~\{~\\
~~int~l~=~0,~u~=~n$-$1;~\\
~~\begin{slshape}/*@~\textbf{loop}~\textbf{invariant}~0~<=~l~\&{}\&{}~u~<=~n$-$1;~\\
~~~~@~\textbf{loop}~\textbf{variant}~u$-$l;~\\
~~~~@*/\end{slshape}~\\
~~\textbf{while}~(l~<=~u)~\{~\\
~~~~int~m~=~l~+~(u~$-$~l)~/~2;~\\
~~~~\textbf{if}~(t[m]~<~v)~\\
~~~~~~l~=~m~+~1;~\\
~~~~\textbf{else}~\textbf{if}~(t[m]~>~v)~\\
~~~~~~u~=~m~$-$~1;~\\
~~~~\textbf{else}~\textbf{return}~m;~\\
~~\}~\\
~~\textbf{return}~$-$1;~\\
\}~\\
\end{flushleft}