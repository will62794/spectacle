## Defining Animations

Spectacle currently provides support for creating animations/visualizations of specifications in a relatively simple and ergonomic manner.

If you want to create an animation for a specification `spec.tla`, the recommended way is to create a separate file `spec_anim.tla` that extends `spec` and contains the animation definition. This convention allows visualizations to be defined separately from a main spec, avoiding pollution of standard specifications with visualization specific details.

Currently, an animation is defined by defining an `AnimView` definition that is defined as an expression that produces an SVG element as a function of your spec's state variables. You can see a simple example of in the [`lockserver`](../specs/lockserver.tla) and [`lockserver_anim`](../specs/lockserver_anim.tla) specs.

Note that you can also define an animation inline in your spec if you desire, by simply defining an `AnimView` definition. This will also be automatically detected and loaded as a visualization. If such an inline animation exists, this will take precedence over any external animations defined in an accompanying `spec_anim.tla` file.

For defining SVG elements, you can currently use the existing definitions in the `SVG` module, which can be automatically extended and includes the definitions contained here. There are also some experimental additions to these raw SVG elements that allow for higher level visualization constructs like directed graphs (see example), which may be modified or extended in the future.