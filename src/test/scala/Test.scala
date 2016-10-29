import com.github.luzhuomi.regex.deriv.RE._
import com.github.luzhuomi.regex.deriv.Common._
import com.github.luzhuomi.regex.deriv.diagnosis.Ambiguity._
import com.github.luzhuomi.regex.deriv.diagnosis.Universality._

object Test 
{
	def main(arg:Array[String]):Unit = 
	{
		// println(diagnose("^([a-zA-Z0-9_\\.\\-])+\\@(([a-zA-Z0-9\\-])+\\.)+([a-zA-Z0-9]{2,4})+$"))		
		println(universal(ascii,Seq(Star(Any, Greedy), Star(Any,Greedy))))
	}
}