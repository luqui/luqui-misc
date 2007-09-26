package com.learningrx.Screens
{
	import flash.display.Sprite;

	public class Screen extends Sprite
	{
		protected var _Parent:Sprite;

		public function Screen(pParent:Sprite)
		{
			_Parent = pParent;
		}
	}
}