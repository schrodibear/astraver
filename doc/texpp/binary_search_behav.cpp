\begin{flushleft}\ttfamily\upshape
%BEGIN LATEX
\parindent 0pt
%END LATEX
\begin{slshape}/*@~\textbf{requires}~n~>=~0~\&{}\&{}~\textbf{\char'134 valid\_{}range}(t,0,n$-$1);~\\
~~@~\textbf{behavior}~success:~\\
~~@~~~\textbf{assumes}~\begin{slshape}\rmfamily\color{darkgreen}//~array~t~is~sorted~in~increasing~order\end{slshape}~\\
~~@~~~~~\textbf{\char'134 forall}~integer~k1,~k2;~0~<=~k1~<=~k2~<=~n$-$1~==>~t[k1]~<=~t[k2];~\\
~~@~~~\textbf{assumes}~\begin{slshape}\rmfamily\color{darkgreen}//~v~appears~somewhere~in~the~array~t\end{slshape}~\\
~~@~~~~~\textbf{\char'134 exists}~integer~k;~0~<=~k~<=~n$-$1~\&{}\&{}~t[k]~==~v;~\\
~~@~~~\textbf{ensures}~0~<=~\textbf{\char'134 result}~<=~n$-$1;~\\
~~@~\textbf{behavior}~failure:~\\
~~@~~~\textbf{assumes}~\begin{slshape}\rmfamily\color{darkgreen}//~v~does~not~appear~anywhere~in~the~array~t\end{slshape}~\\
~~@~~~~~\textbf{\char'134 forall}~integer~k;~0~<=~k~<=~n$-$1~==>~t[k]~!=~v;~\\
~~@~~~\textbf{ensures}~\textbf{\char'134 result}~==~$-$1;~\\
~~@*/\end{slshape}~\\
int~binary\_{}search(long~t[],~int~n,~long~v)~\{~\\
~~int~l~=~0,~u~=~n$-$1;~\\
~~\begin{slshape}/*@~\textbf{loop}~\textbf{invariant}~0~<=~l~\&{}\&{}~u~<=~n$-$1;~\\
~~~~@~\textbf{for}~success:~\\
~~~~@~~~\textbf{loop}~\textbf{invariant}~\\
~~~~@~~~~~\textbf{\char'134 forall}~integer~k;~0~<=~k~<~n~\&{}\&{}~t[k]~==~v~==>~l~<=~k~<=~u;~\\
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