import com.github.luzhuomi.regex.deriv.diagnosis.Ambiguity._

object Test 
{
	def main(arg:Array[String]):Unit = 
	{
		println(diagnose("^([a-zA-Z0-9_\\.\\-])+\\@(([a-zA-Z0-9\\-])+\\.)+([a-zA-Z0-9]{2,4})+$"))		
	}
}