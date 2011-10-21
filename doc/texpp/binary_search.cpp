\begin{flushleft}\ttfamily\upshape
%BEGIN LATEX
\parindent 0pt
%END LATEX
~\\
\begin{slshape}/*@~\textbf{lemma}~mean\_{}1~:~\textbf{\char'134 forall}~integer~x,~int~y;~x~<=~y~==>~x~<=~(x+y)/2~<=~y;~*/\end{slshape}~\\
~\\
\begin{slshape}/*@~\textbf{requires}~\\
~~@~~~n~>=~0~\&{}\&{}~\textbf{\char'134 valid\_{}range}(t,0,n$-$1)~\&{}\&{}~\\
~~@~~~\textbf{\char'134 forall}~integer~k1,~int~k2;~0~<=~k1~<=~k2~<=~n$-$1~==>~t[k1]~<=~t[k2];~\\
~~@~\textbf{ensures}~\\
~~@~~~(\textbf{\char'134 result}~>=~0~\&{}\&{}~t[\textbf{\char'134 result}]~==~v)~||~\\
~~@~~~(\textbf{\char'134 result}~==~$-$1~\&{}\&{}~\textbf{\char'134 forall}~integer~k;~0~<=~k~<~n~==>~t[k]~!=~v);~\\
~~@*/\end{slshape}~\\
int~binary\_{}search(int*~t,~int~n,~int~v)~\{~\\
~~int~l~=~0,~u~=~n$-$1,~p~=~$-$1;~\\
~~\begin{slshape}/*@~\textbf{loop}~\textbf{invariant}~\\
~~~~@~~~0~<=~l~\&{}\&{}~u~<=~n$-$1~\&{}\&{}~$-$1~<=~p~<=~n$-$1~\\
~~~~@~~~\&{}\&{}~(p~==~$-$1~==>~\textbf{\char'134 forall}~integer~k;~0~<=~k~<~n~==>~t[k]~==~v~==>~l~<=~k~<=~u)~\\
~~~~@~~~\&{}\&{}~(p~>=~0~==>~t[p]==v);~\\
~~~~@~\textbf{loop}~\textbf{variant}~u$-$l;~\\
~~~~@*/\end{slshape}~\\
~~\textbf{while}~(l~<=~u)~\{~\\
~~~~int~m~=~(l~+~u)~/~2;~\\
~~~~\begin{slshape}//@~assert~l~<=~m~<=~u;\end{slshape}~\\
~~~~\textbf{if}~(t[m]~<~v)~\\
~~~~~~l~=~m~+~1;~\\
~~~~\textbf{else}~\textbf{if}~(t[m]~>~v)~\\
~~~~~~u~=~m~$-$~1;~\\
~~~~\textbf{else}~\{~\\
~~~~~~p~=~m;~\textbf{break};~\\
~~~~\}~\\
~~\}~\\
~~\textbf{return}~p;~\\
\}~\\
~\\
\begin{slshape}\rmfamily\color{darkgreen}/*~~\\
Local~Variables:~\\
compile$-$command:~"PPCHOME=../..~LC\_{}ALL=C~make~binary\_{}search"~\\
End:~\\
*/\end{slshape}~\\
\end{flushleft}