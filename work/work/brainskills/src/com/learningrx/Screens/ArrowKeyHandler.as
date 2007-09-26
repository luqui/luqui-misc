package com.learningrx.Screens
{
	import flash.events.KeyboardEvent;
	import flash.ui.Keyboard;

	import com.learningrx.*

	public class ArrowKeyHandler
	{
		private const ARROW_KEY_CODES:Object = 
		{
			up: Keyboard.UP, 
			down: Keyboard.DOWN,
		   left: Keyboard.LEFT, 
			right: Keyboard.RIGHT
		};

		private var _Parent:Game;
		private var _Enabled:Boolean;
	
		public function ArrowKeyHandler(pParent:Game)
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
		
		private function GetDirectionFromArrowCharCode(pCharCode:Number):String
		{
			for (var direction:String in ARROW_KEY_CODES)
			{
				if (ARROW_KEY_CODES[direction] == pCharCode)
				{
					return direction;
				}
			}
			return null;
		}
		
		private function OnKeyDown(pEvent:KeyboardEvent):void
		{
			var direction:String = GetDirectionFromArrowCharCode(pEvent.keyCode);
			if (_Enabled && null != direction)
			{
				_Parent.OnArrowKeyPressed(direction);
			}
		}
	}
}