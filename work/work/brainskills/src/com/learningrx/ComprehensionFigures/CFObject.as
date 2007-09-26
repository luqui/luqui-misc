package com.learningrx.ComprehensionFigures
{
	import flash.display.Sprite;
	import flash.utils.getDefinitionByName;

	import com.learningrx.ComprehensionFigures.Figure;
	import com.learningrx.Utilities;

	public class CFObject extends Figure
	{
		private var _objectMC:Sprite;

		public function CFObject(pObjectName:String)
		{
			super(pObjectName);
			var classDefinition:Object = getDefinitionByName("Object_" + Utilities.RemoveSpaces(Utilities.Capitalize(pObjectName, true)));
			_objectMC = new classDefinition();
			this.addChild(_objectMC);
		}
	}		
}