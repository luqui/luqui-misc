package com.learningrx.Screens
{
	import flash.media.SoundTransform;
	import flash.display.Sprite;
	import flash.events.MouseEvent;
	
	import com.learningrx.Utilities;
	import com.learningrx.Screens.Screen;

	public class BasicButton extends Sprite
	{
		protected var _Parent:Sprite;
		protected var _FillMC:Sprite = new Sprite();
		protected var _OutlineMC:Sprite = new Sprite();
		protected var _UnhighlightedFillingColor:Number = 0xFFFFFF;
		protected var _HighlightedFillingColor:Number = 0xCCCCCC;
		protected var _LineColor:Number = 0x000000;
		protected var _LineThickness:Number = 2;
		protected var _CornerRadius:uint = 2;
		protected var _Width:uint = 100;
		protected var _Height:uint = 100;
		protected var _MouseDown:Boolean = false;
		protected var _ClickSound:Sound_Click = new Sound_Click();
		protected var _Enabled:Boolean = true;
		
		public function BasicButton(pParent:Sprite)
		{
			_Parent = pParent;
			Utilities.AddChildToDisplayList(this, _FillMC);
			Utilities.AddChildToDisplayList(this, _OutlineMC);
			AddMouseHandlers();
		}
		
		protected function Init():void
		{
			DrawOutline(_LineThickness);
			DrawFill(_UnhighlightedFillingColor);
		}
		
		public function Highlight():void
		{
			DrawFill(_HighlightedFillingColor);
		}
		
		public function Unhighlight():void
		{
			DrawFill(_UnhighlightedFillingColor);
		}

		public function Select():void
		{
			DrawOutline(_LineThickness + 1);
		}
		
		public function Unselect():void
		{
			DrawOutline(_LineThickness);
		}

		public function Enable():void
		{
			if (!_Enabled)
			{
				AddMouseHandlers();
				_Enabled = true;
			}
		}

		public function Disable():void
		{
			if (_Enabled)
			{
				RemoveMouseHandlers();
				_Enabled = false;
			}
		}

//--------------------------------------------------------------------

		protected function DoClick():void
		{
			if (_Enabled)
			{
				_ClickSound.play(0, 1, new SoundTransform(0.4, 0));
			}
		}

		protected function DrawOutline(pLineThickness:uint = 2):void
		{
			_OutlineMC.graphics.clear();
			_OutlineMC.graphics.lineStyle(pLineThickness, _LineColor, 100, true, "none", "none", "round");
			_OutlineMC.graphics.drawRoundRect(0, 0, _Width, _Height, _CornerRadius, _CornerRadius);
		}
		
		protected function DrawFill(pFillColor:Number):void
		{
			_FillMC.graphics.clear();
			_FillMC.graphics.lineStyle(_LineThickness, _LineColor, 0, true, "none", "none", "round");
			_FillMC.graphics.beginFill(pFillColor, 100);
			_FillMC.graphics.drawRoundRect(0, 0, _Width, _Height, _CornerRadius, _CornerRadius);
			_FillMC.graphics.endFill();
		}
		
		protected function AddMouseHandlers()
		{
			this.buttonMode = true;
			addEventListener(MouseEvent.MOUSE_OVER, MouseOverHandler);
			addEventListener(MouseEvent.MOUSE_OUT, MouseOutHandler);
			addEventListener(MouseEvent.MOUSE_DOWN, MouseDownHandler);
			addEventListener(MouseEvent.MOUSE_UP, MouseUpHandler);
			addEventListener(MouseEvent.CLICK, MouseClickHandler);
		}

		protected function RemoveMouseHandlers()
		{
			//this.buttonMode = false;
			removeEventListener(MouseEvent.MOUSE_OVER, MouseOverHandler);
			removeEventListener(MouseEvent.MOUSE_OUT, MouseOutHandler);
			removeEventListener(MouseEvent.MOUSE_DOWN, MouseDownHandler);
			removeEventListener(MouseEvent.MOUSE_UP, MouseUpHandler);
			removeEventListener(MouseEvent.CLICK, MouseClickHandler);
		}

		protected function MouseOverHandler(pEvent:MouseEvent):void 
		{
			if (_Enabled)
			{
				Highlight();
			}
		}

		protected function MouseOutHandler(pEvent:MouseEvent):void 
		{
			Unhighlight();
		}

		protected function MouseDownHandler(pEvent:MouseEvent):void 
		{
			//
		}

		protected function MouseUpHandler(pEvent:MouseEvent):void 
		{
			//
		}

		protected function MouseClickHandler(pEvent:MouseEvent):void 
		{
			DoClick();
		}
	}
}