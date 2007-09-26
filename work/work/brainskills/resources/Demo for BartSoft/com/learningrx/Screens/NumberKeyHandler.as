package com.learningrx.Screens
{
	import flash.events.KeyboardEvent;
	import flash.ui.Keyboard;

	import com.learningrx.*

	public class NumberKeyHandler
	{
		private const ASCII_0:Number = 48;

		private var _Parent:Game;
		private var _Enabled:Boolean;
	
		public function NumberKeyHandler(pParent:Game)
		{
			_Parent = pParent;
			_Parent.Parent.AddKeyDownListener(OnKeyDown);
			_Enabled = false;
		}
		
		public function Enable():void
		{
			_Enabled = true;
		}

		public function Disable():void
		{
			_Enabled = false;
		}
		
		public function IsNumberCharCode(pCharCode:Number):Boolean
		{
			return (GetNumberFromCharCode(pCharCode) >= 0 && GetNumberFromCharCode(pCharCode) <= 9);
		}
		
		public function GetNumberFromCharCode(pCharCode:Number):Number
		{
			return pCharCode - ASCII_0;
		}
		
		private function OnKeyDown(pEvent:KeyboardEvent):void
		{
			if (_Enabled && IsNumberCharCode(pEvent.charCode))
			{
				_Parent.OnNumberClicked(GetNumberFromCharCode(pEvent.charCode));
			}
		}
	}
}