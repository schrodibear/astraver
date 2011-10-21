\begin{flushleft}\ttfamily\upshape\parindent 0pt
\verb|#|pragma~JessieIntegerModel(math)~\\
~\\
\verb|#|include~"sorting.h"~\\
~\\
\begin{slshape}/*@~\textbf{requires}~\textbf{\char'134 valid}(t+i)~\&{}\&{}~\textbf{\char'134 valid}(t+j);~\\
~~@~\textbf{assigns}~t[i],t[j];~\\
~~@~\textbf{ensures}~Swap\{Old,Here\}(t,i,j);~\\
~~@*/\end{slshape}~\\
void~swap(int~t[],~int~i,~int~j)~\{~\\
~~int~tmp~=~t[i];~\\
~~t[i]~=~t[j];~\\
~~t[j]~=~tmp;~\\
\}~\\
~~~~~\\
\begin{slshape}/*@~\textbf{requires}~\textbf{\char'134 valid\_{}range}(t,0,n$-$1);~\\
~~@~behavior~sorted:~\\
~~@~~~\textbf{ensures}~Sorted(t,0,n$-$1);~\\
~~@~behavior~permutation:~\\
~~@~~~\textbf{ensures}~Permut\{Old,Here\}(t,0,n$-$1);~\\
~~@*/\end{slshape}~\\
void~min\_{}sort(int~t[],~int~n)~\{~\\
~~int~i,j;~\\
~~int~mi,mv;~\\
~~\textbf{if}~(n~<=~0)~\textbf{return};~\\
~~\begin{slshape}/*@~\textbf{loop}~\textbf{invariant}~0~<=~i~<~n;~\\
~~~~@~\textbf{for}~sorted:~~\\
~~~~@~~\textbf{loop}~\textbf{invariant}~~\\
~~~~@~~~Sorted(t,0,i)~\&{}\&{}~~\\
~~~~@~~~(\textbf{\char'134 forall}~integer~k1,~k2~;~~\\
~~~~@~~~~~~0~<=~k1~<~i~<=~k2~<~n~==>~t[k1]~<=~t[k2])~;~\\
~~~~@~\textbf{for}~permutation:~\\
~~~~@~~\textbf{loop}~\textbf{invariant}~Permut\{Pre,Here\}(t,0,n$-$1);~\\
~~~~@~\textbf{loop}~\textbf{variant}~n$-$i;~\\
~~~~@*/\end{slshape}~\\
~~\textbf{for}~(i=0;~i<n$-$1;~i++)~\{~\\
~~~~\begin{slshape}\rmfamily\color{darkgreen}//~look~for~minimum~value~among~t[i..n$-$1]\end{slshape}~\\
~~~~mv~=~t[i];~mi~=~i;~\\
~~~~\begin{slshape}/*@~\textbf{loop}~\textbf{invariant}~i~<~j~\&{}\&{}~i~<=~mi~<~n;~\\
~~~~~~@~\textbf{for}~sorted:~~\\
~~~~~~@~~\textbf{loop}~\textbf{invariant}~\\
~~~~~~@~~~~mv~==~t[mi]~\&{}\&{}~\\
~~~~~~@~~~~(\textbf{\char'134 forall}~integer~k;~i~<=~k~<~j~==>~t[k]~>=~mv);~\\
~~~~~~@~\textbf{for}~permutation:~\\
~~~~~~@~~\textbf{loop}~\textbf{invariant}~\\
~~~~~~@~~~Permut\{Pre,Here\}(t,0,n$-$1);~\\
~~~~~~@~\textbf{loop}~\textbf{variant}~n$-$j;~\\
~~~~~~@*/\end{slshape}~\\
~~~~\textbf{for}~(j=i+1;~j~<~n;~j++)~\{~\\
~~~~~~\textbf{if}~(t[j]~<~mv)~\{~~\\
~~~~~~~~mi~=~j~;~mv~=~t[j];~~\\
~~~~~~\}~\\
~~~~\}~\\
~~~~swap(t,i,mi);~\\
~~\}~\\
\}~\\
~\\
\end{flushleft}