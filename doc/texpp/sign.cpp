\begin{flushleft}\ttfamily\upshape
%BEGIN LATEX
\parindent 0pt
%END LATEX
\begin{slshape}\rmfamily\color{darkgreen}//~fonction~signe\end{slshape}~\\
\textbf{logic}~float\_{}sign~:~gen\_{}float~$-$>~sign~\\
~\\
\textbf{predicate}~same\_{}sign\_{}real\_{}bool~(s:sign,x:real)~=~\\
~~~~~~~~~~(x~<~0.0~<$-$>~s~=~Negative)~and~~\\
~~~~~~~~~~(x~>~0.0~<$-$>~s~=~Positive)~\\
~\\
\textbf{predicate}~same\_{}sign\_{}real~(x:gen\_{}float,y:real)~=~\\
~~~~~~~~~~same\_{}sign\_{}real\_{}bool(float\_{}sign(x),y)~\\
~\\
\textbf{predicate}~same\_{}sign(x:gen\_{}float,y:gen\_{}float)~=~~\\
~~~~~~~~~~float\_{}sign(x)~=~float\_{}sign(y)~\\
~\\
\textbf{predicate}~diff\_{}sign(x:gen\_{}float,y:gen\_{}float)~=~~\\
~~~~~~~~~~float\_{}sign(x)~<>~float\_{}sign(y)~\\
\end{flushleft}