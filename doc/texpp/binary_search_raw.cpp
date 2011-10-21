\begin{flushleft}\ttfamily\upshape
%BEGIN LATEX
\parindent 0pt
%END LATEX
\verb|#|pragma~JessieIntegerModel(math)~\\
\verb|#|pragma~JessieTerminationPolicy(user)~\\
~\\
int~binary\_{}search(long~t[],~int~n,~long~v)~\{~\\
~~int~l~=~0,~u~=~n$-$1;~\\
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