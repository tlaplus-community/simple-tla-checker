package us.tlapl;

public class Constants {
	
	public static final String TLA_FILE_SUFFIX = ".tla";
	
	public static final String[] STANDARD_MODULES = new String[] {
		"Naturals",
		"Sequences",
		"FiniteSets",
		"TLC",
		"Bags",
		"Integers",
		"Reals",
		"Json",
		"Randomization",
		"RealTime",
		"TLCExt",
		"Toolbox"
	};
	
	public static boolean isStandardModule(String moduleName) {
		for (String standardModule : STANDARD_MODULES) {
			if (moduleName.equals(standardModule)) {
				return true;
			}
		}
		return false;
	}
}