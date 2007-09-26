package com.learningrx.VisualPuzzle
{
	import flash.display.Bitmap;
	import flash.display.Sprite;
	import flash.events.MouseEvent;
	import flash.geom.Point;
	import flash.filters.*;
	
	import com.learningrx.Shared.*;
	
	class JigsawPiece extends Sprite
	{
		private const BORDER_COLOR:Number = 0x000000;
		private const BORDER_WIDTH:Number = 0;
		private const BORDER_ALPHA:Number = 100;
		private const LIFT_OFFSET:Number = 2;
		private const SCREEN_BORDER_MARGIN:Number = 2;

		private var _Parent:VisualPuzzle;
		private var _BackgroundSprite:Sprite;
		private var _MaskSprite:Sprite;
		private var _ImageBitmap:Bitmap;
		private var _DropShadow:DropShadowFilter;
		private var _Bevel:BevelFilter;
		private var _Pieces:Array;
		private var _Edges:Array;
		private var _MoveDestination:Object;
		private var _MoveSteps:Number = 5;
		private var _Moving:Boolean = false;
		private var _Ambling:Boolean = false;
		private var _Offset:Point;
		private var _WestIndent:Number = 1000000;
		private var _NorthIndent:Number = 1000000;
		private var _EastIndent:Number = 1000000;
		private var _SouthIndent:Number = 1000000;
		private var _MainPiece:Object;
		private var _Lifted:Boolean = false;
		private var _VisibleCenter:Point;
		
		public function JigsawPiece(pParent:VisualPuzzle,
											 pImageBitmap:Bitmap,
											 pEdges:Array,
											 pPieces:Array)
		{
			_Parent = pParent;
			_ImageBitmap = new Bitmap(pImageBitmap.bitmapData);
			_Edges = pEdges;
			_Pieces = pPieces;
			_MainPiece = _Pieces[0];
			CreatePiece();
			InitFilters();
			UpdateIndents();
		}
		
		public function Start()
		{
			Rotate(_MainPiece.rotation);
			_MoveDestination = GetRandomMoveDestination();
			_Moving = true;
			InitMouseListener();
		}
		
		// Piece creation

		private function CreatePiece():void
		{
			_BackgroundSprite = new Sprite();
			_MaskSprite = new Sprite();
			Utilities.Show(this, _BackgroundSprite, _MaskSprite);
			Utilities.Show(_BackgroundSprite, _ImageBitmap);
			DrawMask();
			_BackgroundSprite.mask = _MaskSprite;
		}

		private function DrawMask():void
		{
			for (var i:Number = 0; i < _Pieces.length; ++i)
			{
				DrawPieceMask(i);
			}
		}
		
		private function DrawPieceMask(pIndex:Number):void
		{
			pIndex = Math.max(pIndex, -1);
			var outlineSprite:Sprite = new Sprite();
			outlineSprite.graphics.clear();
			outlineSprite.graphics.lineStyle(BORDER_WIDTH, BORDER_COLOR, BORDER_ALPHA, true);
			outlineSprite.graphics.moveTo(0, 0);
			outlineSprite.graphics.beginFill(BORDER_COLOR);
			DrawEdge(outlineSprite, "top", _Pieces[pIndex].topEdge);
			DrawEdge(outlineSprite, "right", _Pieces[pIndex].rightEdge);
			DrawEdge(outlineSprite, "bottom", _Pieces[pIndex].bottomEdge);
			DrawEdge(outlineSprite, "left", _Pieces[pIndex].leftEdge);
			outlineSprite.graphics.endFill();
			outlineSprite.x = _Pieces[pIndex].x;
			outlineSprite.y = _Pieces[pIndex].y;
			outlineSprite.scaleX = _Pieces[pIndex].width / 100;
			outlineSprite.scaleY = _Pieces[pIndex].height / 100;
			Utilities.Show(_MaskSprite, outlineSprite);
		}
		
		private function DrawEdge(pOutlineSprite:Sprite,
										  pSide:String,
										  pEdgeIndex:Number):void
		{
			var direction:Number;
			if (pEdgeIndex < 0)
			{
				direction = -1;
			}
			else
			{
				direction = 1;
			}
			var points:Array = _Edges[Math.abs(pEdgeIndex)];
			switch (pSide)
			{
				case 'top':
					for (var i:Number = 1; i < points.length; ++i)
					{
						if (i == 0)
						{
							pOutlineSprite.graphics.moveTo(points[i][0], points[i][1]);
 						   continue;
						}
						else if (points[i].length == 2)
						{
							pOutlineSprite.graphics.lineTo(points[i][0], direction * points[i][1]);
 						   continue;
						}
						else
						{
							pOutlineSprite.graphics.curveTo(points[i][2], direction * points[i][3],
																	  points[i][0], direction * points[i][1]);
						}
					}
					break;
				case 'right':
					for (i = 1; i < points.length; ++i)
					{
						if (points[i].length == 2)
						{
							pOutlineSprite.graphics.lineTo(100 - direction * points[i][1], points[i][0]);
 						   continue;
						}
						else
						{
							pOutlineSprite.graphics.curveTo(100 - direction * points[i][3],
																	  points[i][2], 100 - direction * points[i][1], points[i][0]);
						}
					}
					break;
				case 'bottom':
					for (i = points.length - 1; i > 0; --i)
					{
						if (points[i].length == 2)
						{
							pOutlineSprite.graphics.lineTo(points[i - 1][0], 100 - direction * points[i - 1][1]);
						}
						else
						{
							pOutlineSprite.graphics.curveTo(points[i][2], 100 - direction * points[i][3],
																	  points[i - 1][0], 100 - direction * points[i - 1][1]);
						}
					}
					break;
				case 'left':
					for (i = points.length - 1; i > 0; --i)
					{
						if (points[i].length == 2)
						{
							pOutlineSprite.graphics.lineTo(direction * points[i - 1][1], points[i - 1][0]);
						}
						else
						{
							pOutlineSprite.graphics.curveTo(direction * points[i][3], points[i][2],
																	  direction * points[i - 1][1], points[i - 1][0]);
						}
					}
					break;
			}
		}

		public function Absorb(pPiece:JigsawPiece):void
		{
			if (pPiece != this)
			{
				var currentPieces:Number = _Pieces.length;
				_Pieces = _Pieces.concat(pPiece.Pieces);
				for (var i = currentPieces; i < _Pieces.length; ++i)
				{
					DrawPieceMask(i);
				}
				UpdateIndents();
				MoveTo(this.x, this.y);
			}
		}

		private function InitFilters():void
		{
			_Bevel = new BevelFilter();
			_Bevel.distance = 3;
			_Bevel.angle = 45;
			_Bevel.highlightColor = 0xFFFFFF;
			_Bevel.highlightAlpha = .9;
			_Bevel.shadowColor = 0x000000;
			_Bevel.shadowAlpha = .9;
			_Bevel.blurX = 3;
			_Bevel.blurY = 3;
			_Bevel.strength = 1;
			_Bevel.quality = BitmapFilterQuality.HIGH;
			_Bevel.type = BitmapFilterType.INNER;
			_Bevel.knockout = false;
			_DropShadow = new DropShadowFilter();
			_DropShadow.distance = 1;
			_DropShadow.color = 0x000000;
			_DropShadow.angle = 45;
			_DropShadow.alpha = .85;
			_DropShadow.blurX = 3;
			_DropShadow.blurY = 3;
			_DropShadow.quality = BitmapFilterQuality.HIGH;
			_DropShadow.knockout = false;
			this.filters = [_Bevel, _DropShadow];
		}

		public function RemoveMask()
		{
			Utilities.Hide(this, _MaskSprite);
			_BackgroundSprite.mask = null;
			_MaskSprite = null;
		}
		
		// Motion
		
		public function BeginMoving(pX:Number,
											 pY:Number):void
		{
			_MoveDestination =
			{
				x: pX,
				y: pY
			};
			_Moving = true;
		}
		
		public function StopMoving():void
		{
			_Moving = false;
		}
		
		public function Animate()
		{
			if (_Moving)
			{
				AnimatedMove();
			}
		}
		
		public function MoveTo(pX:Number,
									  pY:Number):void
		{
			this.x = ConstrainX(pX);
			this.y = ConstrainY(pY);
		}
		
		public function GetRandomMoveDestination():Object
		{
			var randomMoveDestination:Object =
			{
				x: Utilities.RandRange(SCREEN_BORDER_MARGIN - GetLeft(this.rotation),
											  _Parent.BackgroundWidth - SCREEN_BORDER_MARGIN - GetRight(this.rotation)),
				y: Utilities.RandRange(SCREEN_BORDER_MARGIN - GetTop(this.rotation),
											  _Parent.ScoreAndDividerY - SCREEN_BORDER_MARGIN - GetBottom(this.rotation))
			};
			return randomMoveDestination;
		}
		
		private function ConstrainX(pX:Number):Number
		{
			var offset:Number = 0;
			if (_Lifted)
			{
				offset = -LIFT_OFFSET;
			}
			return Utilities.Between(pX, SCREEN_BORDER_MARGIN - GetLeft(this.rotation) + offset,
											 _Parent.BackgroundWidth - SCREEN_BORDER_MARGIN -
											 GetRight(this.rotation) + offset);
		}
		
		private function ConstrainY(pY:Number):Number
		{
			var offset:Number = 0;
			if (_Lifted)
			{
				offset = -LIFT_OFFSET;
			}
			return Utilities.Between(pY, SCREEN_BORDER_MARGIN - GetTop(this.rotation) + offset,
											 _Parent.ScoreAndDividerY - SCREEN_BORDER_MARGIN -
											 GetBottom(this.rotation) + offset);
		}
		
		public function Lift():void
		{
			if (!_Lifted)
			{
				MoveTo(this.x - LIFT_OFFSET, this.y - LIFT_OFFSET);
				_DropShadow.distance = 6;
				_DropShadow.blurX = 12;
				_DropShadow.blurY = 12;
				this.filters = [_Bevel, _DropShadow];
				_Moving = false;
				_Lifted = true;
			}
		}

		public function Drop():void
		{
			if (_Lifted)
			{
				MoveTo(this.x + LIFT_OFFSET, this.y + LIFT_OFFSET);
				_DropShadow.distance = 1;
				_DropShadow.blurX = 3;
				_DropShadow.blurY = 3;
				this.filters = [_Bevel, _DropShadow];
				_Lifted = false;
			}
		}

		private function Amble():void
		{
			if (_Ambling)
			{
				_Moving = true;
			}
		}
		
		private function AnimatedMove():void
		{
			if (Math.abs(this.x - _MoveDestination.x) < 1 &&
				 Math.abs(this.y - _MoveDestination.y) < 1)
			{
				MoveTo(_MoveDestination.x, _MoveDestination.y);
				if (_Ambling)
				{
					Rotate(Utilities.RandRange(0, 3) * 90);
					_MoveDestination = GetRandomMoveDestination();
					_MoveSteps = Utilities.RandRange(5, 20);
				}
				else
				{
					_Moving = false;
				}
			}
			else
			{
				MoveTo(this.x + (_MoveDestination.x - this.x) / _MoveSteps,
						 this.y + (_MoveDestination.y - this.y) / _MoveSteps);
			}
		}

		// Mouse
		
		private function InitMouseListener():void
		{
			this.addEventListener(MouseEvent.MOUSE_DOWN, OnMouseDown);
		}

		private function OnMouseDown(pEvent:MouseEvent):void
		{
			_Parent.ChildPressed(this);
		}
		
		public function RemoveMouseListener():void
		{
			this.removeEventListener(MouseEvent.MOUSE_DOWN, OnMouseDown);
		}

		// Getters & Setters

		private function get WestToCenter():Number
		{
			return _WestIndent + (_Parent.ImageWidth - (_EastIndent + _WestIndent)) / 2;
		}
		
		private function get EastToCenter():Number
		{
			return _Parent.ImageWidth - WestToCenter;
		}
		
		private function get NorthToCenter():Number
		{
			return _NorthIndent + (_Parent.ImageHeight - (_NorthIndent + _SouthIndent)) / 2;
		}
		
		private function get SouthToCenter():Number
		{
			return _Parent.ImageHeight - NorthToCenter;
		}
		
		private function get PiecesHeight():Number
		{
			return _SouthIndent - _NorthIndent;
		}
		
		private function get PiecesWidth():Number
		{
			return _WestIndent - _EastIndent;
		}
		
		public function get Moving():Boolean
		{
			return _Moving;
		}
		
		public function get Ambling():Boolean
		{
			return _Ambling;
		}
		
		public function set Ambling(pAmbling:Boolean):void
		{
			_Ambling = pAmbling;
			if (pAmbling)
			{
				Amble();
				_MoveSteps = Utilities.RandRange(5, 20);
			}
		}
		
		public function get MaskSprite():Sprite
		{
			return _MaskSprite;
		}
		
		// Rotation code
		
		public function Rotate(pRotation:Number):void
		{
			this.x -= GetOffset(this.rotation).x;
			this.y -= GetOffset(this.rotation).y;
			this.rotation = (pRotation + this.rotation) % 360;
			this.x = ConstrainX(this.x + GetOffset(this.rotation).x);
			this.y = ConstrainY(this.y + GetOffset(this.rotation).y);
		}
		
		private function UpdateIndents():void
		{
			var interlockWidth:Number = 16 * _MainPiece.width / 100;
			var interlockHeight:Number = 16 * _MainPiece.height / 100;
			for each (var piece:Object in _Pieces)
			{
				_WestIndent = Math.min(_WestIndent, piece.x - (piece.col == 0 ? 0 : interlockWidth));
				_NorthIndent = Math.min(_NorthIndent, piece.y - (piece.row == 0 ? 0 : interlockHeight));
				_EastIndent = Math.min(_EastIndent, _Parent.ImageWidth - (piece.x + piece.width +
											  (piece.col == _Parent.Columns - 1 ? 0 : interlockWidth)));
				_SouthIndent = Math.min(_SouthIndent, _Parent.ImageHeight - (piece.y + piece.height +
												(piece.row == _Parent.Rows - 1 ? 0 : interlockHeight)));
			}
		}
		
		private function GetVisibleCenter(pRotation:Number):Point
		{
			var centerPoint:Point = new Point(this.x + WestToCenter, this.y + NorthToCenter);
			centerPoint.x -= GetOffset(pRotation).x;
			centerPoint.y -= GetOffset(pRotation).y;
			return centerPoint;
		}

		public function GetLeft(pRotation:Number):Number
		{
			var left:Number;
			switch (pRotation)
			{
				case 0:
					left = _WestIndent;
					break;
				case 90:
					left = _SouthIndent - _Parent.ImageHeight;
					break;
				case 180:
					left = _EastIndent - _Parent.ImageWidth;
					break;
				case 270:
				case -90:
					left = _NorthIndent;
					break;
			}
			return left;
		}
		
		public function GetTop(pRotation:Number):Number
		{
			var top:Number;
			switch (pRotation)
			{
				case 0:
					top = _NorthIndent;
					break;
				case 90:
					top = _WestIndent;
					break;
				case 180:
					top = _SouthIndent - _Parent.ImageHeight;
					break;
				case 270:
				case -90:
					top = _EastIndent - _Parent.ImageWidth;
					break;
			}
			return top;
		}
		
		public function GetRight(pRotation:Number):Number
		{
			var right:Number;
			switch (pRotation)
			{
				case 0:
					right = _Parent.ImageWidth - _EastIndent;
					break;
				case 90:
					right = - _NorthIndent;
					break;
				case 180:
					right = - _WestIndent;
					break;
				case 270:
				case -90:
					right = _Parent.ImageHeight - _SouthIndent;
					break;
			}
			return right;
		}
		
		
		public function GetBottom(pRotation:Number):Number
		{
			var bottom:Number;
			switch (pRotation)
			{
				case 0:
					bottom = _Parent.ImageHeight - _SouthIndent;
					break;
				case 90:
					bottom = _Parent.ImageWidth - _EastIndent;
					break;
				case 180:
					bottom = - _NorthIndent;
					break;
				case 270:
				case -90:
					bottom = - _WestIndent;
					break;
			}
			return bottom;
		}
		
		public function GetOffset(pRotation:Number):Point
		{
			var offset:Point = new Point(0, 0);
			switch (pRotation)
			{
				case 90:
					offset.x = _Parent.ImageHeight + WestToCenter - SouthToCenter;
					offset.y = NorthToCenter - WestToCenter;
					break;
				case 180:
					offset.x = _Parent.ImageWidth + WestToCenter - EastToCenter;
					offset.y = _Parent.ImageHeight + NorthToCenter - SouthToCenter;
					break;
				case 270:
				case -90:
					offset.x = WestToCenter - NorthToCenter;
					offset.y = _Parent.ImageWidth + NorthToCenter - EastToCenter;
					break;
			}
			return offset;
		}

		public function get Pieces():Array
		{
			return _Pieces;
		}
		
		public function get PiecesCount():Number
		{
			return _Pieces.length;
		}
	}
}
