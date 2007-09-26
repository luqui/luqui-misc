package com.learningrx
{
   import flash.display.Stage;
   import flash.display.Sprite;
   import flash.events.*;
   import flash.events.KeyboardEvent;
   
   public class Key extends Sprite
	{
      private var _KeysDown:Object = new Object();
		private var _KeyDownListeners:Array;
		private var _Stage:Stage
       
      public function Key(pStage:Stage) 
		{
         _Stage = pStage;
         _Stage.focus = this;
			_Stage.addEventListener(KeyboardEvent.KEY_DOWN, _Key.OnKeyDown);
			_Stage.addEventListener(KeyboardEvent.KEY_DOWN, _Key.OnKeyDown, true);
         _Stage.addEventListener(KeyboardEvent.KEY_UP, _Key.OnKeyUp);
         _Stage.addEventListener(Event.DEACTIVATE, ClearKeys);
			_KeyDownListeners = new Array();
      }
       
      public function AddKeyDownListener(pFunction:Function):void 
		{
         if (!Utilities.ArrayContains(_KeyDownListeners, pFunction))
			{
				_KeyDownListeners.push(pFunction);
			}
      }
       
      public function RemoveKeyDownListener(pFunction:Function):void 
		{
         if (Utilities.ArrayContains(_KeyDownListeners, pFunction))
			{
				Utilities.RemoveElementFromArray(_KeyDownListeners, pFunction);
			}
      }
       
      public function IsDown(pKeyCode:uint):Boolean 
		{
         return Boolean(pKeyCode in _KeysDown);
      }
   

      private function OnKeyDown(pEvent:KeyboardEvent):void 
		{
			if (pEvent.eventPhase == EventPhase.BUBBLING_PHASE)
			{
				return;
			}
         trace('OnKeyDown');
			_KeysDown[pEvent.keyCode] = true;
			for (var i:Number = 0; i < _KeyDownListeners.length; ++i)
			{
				_KeyDownListeners[i](pEvent);
			}
      }
       
      private function OnKeyUp(pEvent:KeyboardEvent):void 
		{
         if (pEvent.keyCode in _KeysDown) 
			{
            delete _KeysDown[pEvent.keyCode];
         }
      }
       
      // clear all keys in _KeysDown since the player cannot
      // detect keys being pressed or released when not focused
      private function ClearKeys(pEvent:Event):void 
		{
         _KeysDown = new Object();
      }
    }
}